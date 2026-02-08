using GMap.NET;
using GMap.NET.MapProviders;
using GMap.NET.WindowsForms;
using GMap.NET.WindowsForms.Markers;

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Drawing;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Net.Sockets;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using System.Xml;

namespace RobinRadar
{
    public sealed class TrackSample
    {
        public string TargetId { get; set; } = "";
        public DateTime TimestampUtc { get; set; } = DateTime.MinValue;

        public double LatitudeDeg { get; set; } = double.NaN;
        public double LongitudeDeg { get; set; } = double.NaN;
        public double AltitudeM { get; set; } = double.NaN;

        public double SpeedMps { get; set; } = double.NaN;
        public double AzimuthDeg { get; set; } = double.NaN;
        public double ElevationDeg { get; set; } = double.NaN;

        public double Score { get; set; } = double.NaN;
        public string Classification { get; set; } = "UNKNOWN";

        // Debug columns (optional)
        public double? IntervalMs { get; set; } = null;
        public bool SameTimestampFlag { get; set; } = false;
        public bool OutOfOrderFlag { get; set; } = false;

        // Kalman derived values (grid)
        public double? KfLatDeg { get; set; } = null;
        public double? KfLonDeg { get; set; } = null;
        public double? KfSpeedMps { get; set; } = null;
        public double? KfHeadingDeg { get; set; } = null;
    }

    public partial class Form1 : Form
    {
        // =========================
        // MODE
        // =========================
        private enum DataMode { SimulationFile, Ethernet }

        // Switch here:
        private const DataMode MODE = DataMode.Ethernet;

        // =========================
        // SIM CONFIG
        // =========================
        private const string SIM_XML_PATH = "SIM1.xml";
        private const bool SIM_REPEAT = false;
        private const double SIM_TIME_SCALE = 1.0;
        private const int SIM_MIN_DELAY_MS = 30;
        private const int SIM_MAX_DELAY_MS = 4000;

        // =========================
        // ETHERNET CONFIG
        // =========================
        private const string ROBIN_HOST = "192.168.1.15";
        private const int ROBIN_PORT = 16810;
        private const int RECONNECT_DELAY_MS = 600;
        private const int TCP_READ_BUF_BYTES = 32 * 1024;

        // =========================
        // FILTERS
        // =========================
        private const double SCORE_MIN = 0.80;

        private string _autoCsvPath = null;

        // =========================
        // LIMITS
        // =========================
        private const int GRID_MAX_ROWS = 20000;
        private const int MAP_MAX_MARKERS = 50000;

        // =========================
        // VISUAL
        // =========================
        private const int RENDER_FPS_INTERVAL_MS = 50;
        private const int UI_DRAIN_INTERVAL_MS = 15;
        private const int UI_DRAIN_BUDGET_MS = 6;

        private const int DOT_SIZE_MEAS = 10;
        private const int DOT_SIZE_MID = 6;
        private const int DOT_SIZE_CURRENT = 15;
        private const int DOT_SIZE_KF = 8; // حجم نقاط الكالمان

        private const bool DRAW_MIDPOINTS = false; // تم تعطيل رسم الميد بوينت
        private const bool DRAW_CURRENT_MARKER = true;

        // =========================
        // 100ms PREDICTION
        // =========================
        private const int PRED_TICK_MS = 100;
        private const double PRED_STEP_SEC = 0.100;
        private const int PRED_TICK_BUDGET_MS = 6;
        private const int ACTIVE_TARGET_TTL_MS = 3000;

        // =========================
        // KALMAN
        // =========================
        private const bool KF_ENABLE = true;

        private const bool KF_USE_MIDPOINT_PSEUDO_MEAS = true;
        private const double KF_MEAS_SIGMA_M = 3.0;
        private const double KF_MID_SIGMA_MULT = 2.5;

        private const double KF_ACCEL_SIGMA_MPS2 = 4.0;

        private const bool KF_INJECT_MEAS_VELOCITY = true;
        private const double KF_VEL_INJECT_BLEND = 0.35;
        private const double KF_VEL_CLAMP_MPS = 45.0;

        private const bool KF_ROUTE_ON_MEASUREMENTS_ONLY = true;
        private const int KF_ROUTE_MAX_POINTS = 30000;

        // =========================
        // MAP DEFAULTS
        // =========================
        private double latitude = 51.44634770;
        private double longitude = 4.33721663;
        private int _zoomValue = 15;

        private GMapOverlay _measuredOverlay;
        private GMapOverlay _midpointOverlay;
        private GMapOverlay _currentOverlay;
        private GMapOverlay _sensorOverlay;

        private GMapOverlay _kfOverlay;
        private GMapOverlay _kfCurrentOverlay;

        private GMapMarker _sensorMarker;

        private Bitmap _robinBmp;
        private Bitmap _dotMeasBmp;
        private Bitmap _dotMidBmp;
        private Bitmap _dotCurrentBmp;
        private Bitmap _dotKfCurrentBmp;
        private Bitmap _dotKfBmp; // نقاط الكالمان

        // =========================
        // SENSOR
        // =========================
        private bool _sensorInit = false;
        private double _sensorLatDeg = double.NaN;
        private double _sensorLonDeg = double.NaN;

        // =========================
        // UI DATA
        // =========================
        private readonly BindingList<TrackSample> _gridList = new BindingList<TrackSample>();

        // =========================
        // MEASURED VISUAL STATE
        // =========================
        private readonly Dictionary<string, PointLatLng> _lastPosByTargetId =
            new Dictionary<string, PointLatLng>(StringComparer.Ordinal);

        private readonly Dictionary<string, GMapMarker> _currentMarkerByTargetId =
            new Dictionary<string, GMapMarker>(StringComparer.Ordinal);

        // =========================
        // KALMAN STATE (UI thread only)
        // =========================
        private readonly Dictionary<string, LocalFrameEnu> _frameById =
            new Dictionary<string, LocalFrameEnu>(StringComparer.Ordinal);

        private readonly Dictionary<string, KalmanCv2D> _kfById =
            new Dictionary<string, KalmanCv2D>(StringComparer.Ordinal);

        private readonly Dictionary<string, GMapMarker> _kfMarkerById =
            new Dictionary<string, GMapMarker>(StringComparer.Ordinal);

        private readonly Dictionary<string, List<GMarkerGoogle>> _kfMarkersById =
            new Dictionary<string, List<GMarkerGoogle>>(StringComparer.Ordinal);

        private readonly Dictionary<string, PointLatLng> _kfLastMeasPosById =
            new Dictionary<string, PointLatLng>(StringComparer.Ordinal);

        private struct LastMeasEnu
        {
            public bool Has;
            public DateTime TimeUtc;
            public double X, Y;
        }

        private readonly Dictionary<string, LastMeasEnu> _kfLastMeasEnuById =
            new Dictionary<string, LastMeasEnu>(StringComparer.Ordinal);

        private readonly Dictionary<string, DateTime> _activeUntilUtcById =
            new Dictionary<string, DateTime>(StringComparer.Ordinal);

        private readonly Dictionary<string, double> _predAccumSecById =
            new Dictionary<string, double>(StringComparer.Ordinal);

        private readonly Dictionary<string, DateTime> _predLastWallUtcById =
            new Dictionary<string, DateTime>(StringComparer.Ordinal);

        // =========================
        // THREADING
        // =========================
        private CancellationTokenSource _cts;

        private sealed class Message
        {
            public DateTime ArrivalUtc;
            public DateTime FileTsUtc;

            public bool HasGps;
            public double SensorLat, SensorLon;

            public List<TrackSample> Tracks;
        }

        private readonly ConcurrentQueue<Message> _msgQueue = new ConcurrentQueue<Message>();
        private System.Windows.Forms.Timer _uiDrainTimer;
        private System.Windows.Forms.Timer _renderTimer;
        private System.Windows.Forms.Timer _predTimer;

        private bool _startedOnce = false;

        public Form1()
        {
            InitializeComponent();
            Load += Form1_Load;
            Shown += Form1_Shown;
            FormClosing += Form1_FormClosing;

            btnMapZoomPos.Click += btnMapZoomPos_Click;
            btnMapZoomNeg.Click += btnMapZoomNeg_Click;
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            var inv = CultureInfo.InvariantCulture;
            CultureInfo.DefaultThreadCurrentCulture = inv;
            CultureInfo.DefaultThreadCurrentUICulture = inv;
            Thread.CurrentThread.CurrentCulture = inv;
            Thread.CurrentThread.CurrentUICulture = inv;

            InitMap();

            _robinBmp = TryLoadSensorBitmap();
            _dotMeasBmp = CreateDotBitmap(Color.Red, DOT_SIZE_MEAS); // تغيير اللون إلى الأحمر
            _dotMidBmp = CreateDotBitmap(Color.DarkGreen, DOT_SIZE_MID);
            _dotCurrentBmp = CreateRingDotBitmap(Color.Cyan, Color.Black, DOT_SIZE_CURRENT);
            _dotKfCurrentBmp = CreateRingDotBitmap(Color.Yellow, Color.Black, DOT_SIZE_CURRENT);
            _dotKfBmp = CreateDotBitmap(Color.DodgerBlue, DOT_SIZE_KF); // نقاط الكالمان باللون الأزرق

            GridView.AutoGenerateColumns = true;
            GridView.DataSource = _gridList;

            ResetAll();

            _cts = new CancellationTokenSource();

            StartMapRenderTimer();
            StartPredictionTimer();

            if (MODE == DataMode.Ethernet)
                StartUiDrainTimer();
        }

        private void Form1_Shown(object sender, EventArgs e)
        {
            if (_startedOnce) return;
            _startedOnce = true;

            if (MODE == DataMode.Ethernet)
                Task.Run(() => EthernetProducerLoop(_cts.Token));
            else
                Task.Run(() => SimulationPlaybackLoop(_cts.Token));
        }

        private void Form1_FormClosing(object sender, FormClosingEventArgs e)
        {
            try
            {
                if (GridView.Rows.Count > 0)
                {
                    var result = MessageBox.Show(
                        this,
                        "Save track data to CSV before closing?",
                        "Save data",
                        MessageBoxButtons.YesNoCancel,
                        MessageBoxIcon.Question);

                    if (result == DialogResult.Cancel)
                    {
                        e.Cancel = true;
                        return;
                    }

                    if (result == DialogResult.Yes)
                    {
                        if (string.IsNullOrEmpty(_autoCsvPath))
                        {
                            using (var sfd = new SaveFileDialog())
                            {
                                sfd.Filter = "CSV files (*.csv)|*.csv";
                                sfd.FileName = $"RobinRadar_{DateTime.UtcNow:yyyyMMdd_HHmmss}.csv";

                                if (sfd.ShowDialog(this) != DialogResult.OK)
                                {
                                    e.Cancel = true;
                                    return;
                                }

                                _autoCsvPath = sfd.FileName;
                            }
                        }

                        SaveDataGridViewToCsv(GridView, _autoCsvPath);
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show(
                    this,
                    "Failed to save CSV:\n" + ex.Message,
                    "Error",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Error);
            }

            try { _cts?.Cancel(); } catch { }
            try { _uiDrainTimer?.Stop(); } catch { }
            try { _renderTimer?.Stop(); } catch { }
            try { _predTimer?.Stop(); } catch { }

            SafeDispose(ref _robinBmp);
            SafeDispose(ref _dotMeasBmp);
            SafeDispose(ref _dotMidBmp);
            SafeDispose(ref _dotCurrentBmp);
            SafeDispose(ref _dotKfCurrentBmp);
            SafeDispose(ref _dotKfBmp);
        }

        private static void SaveDataGridViewToCsv(DataGridView dgv, string filePath)
        {
            var sb = new StringBuilder(1024 * 1024);

            bool first = true;
            foreach (DataGridViewColumn col in dgv.Columns)
            {
                if (!col.Visible) continue;

                if (!first) sb.Append(',');
                sb.Append(CsvEscape(col.HeaderText));
                first = false;
            }
            sb.AppendLine();

            foreach (DataGridViewRow row in dgv.Rows)
            {
                if (row.IsNewRow) continue;

                first = true;
                foreach (DataGridViewColumn col in dgv.Columns)
                {
                    if (!col.Visible) continue;

                    if (!first) sb.Append(',');

                    object val = row.Cells[col.Index].Value;
                    string text = val == null
                        ? ""
                        : Convert.ToString(val, CultureInfo.InvariantCulture);

                    sb.Append(CsvEscape(text));
                    first = false;
                }
                sb.AppendLine();
            }

            File.WriteAllText(filePath, sb.ToString(), Encoding.UTF8);
        }

        private static string CsvEscape(string s)
        {
            if (string.IsNullOrEmpty(s)) return "";

            bool mustQuote =
                s.Contains(",") ||
                s.Contains("\"") ||
                s.Contains("\r") ||
                s.Contains("\n");

            if (s.Contains("\""))
                s = s.Replace("\"", "\"\"");

            return mustQuote ? $"\"{s}\"" : s;
        }

        private void ResetAll()
        {
            _gridList.Clear();

            _lastPosByTargetId.Clear();
            _currentMarkerByTargetId.Clear();

            _frameById.Clear();
            _kfById.Clear();
            _kfMarkerById.Clear();
            _kfMarkersById.Clear();
            _kfLastMeasPosById.Clear();
            _kfLastMeasEnuById.Clear();

            _activeUntilUtcById.Clear();
            _predAccumSecById.Clear();
            _predLastWallUtcById.Clear();

            _sensorInit = false;
            _sensorMarker = null;

            _measuredOverlay?.Markers.Clear();
            _midpointOverlay?.Markers.Clear();
            _currentOverlay?.Markers.Clear();
            _sensorOverlay?.Markers.Clear();

            _kfOverlay?.Routes.Clear();
            _kfOverlay?.Markers.Clear();
            _kfCurrentOverlay?.Markers.Clear();

            while (_msgQueue.TryDequeue(out _)) { }
        }

        private void InitMap()
        {
            GMaps.Instance.Mode = AccessMode.ServerAndCache;

            map.MapProvider = GMapProviders.GoogleHybridMap;
            map.MinZoom = 2;
            map.MaxZoom = 20;
            map.Zoom = _zoomValue;
            map.Position = new PointLatLng(latitude, longitude);

            map.CanDragMap = true;
            map.DragButton = MouseButtons.Left;
            map.ShowCenter = false;

            _measuredOverlay = new GMapOverlay("measured_points");
            _midpointOverlay = new GMapOverlay("midpoints");
            _kfOverlay = new GMapOverlay("kf_route");
            _currentOverlay = new GMapOverlay("measured_current");
            _kfCurrentOverlay = new GMapOverlay("kf_current");
            _sensorOverlay = new GMapOverlay("sensor");

            map.Overlays.Clear();
            map.Overlays.Add(_measuredOverlay);
            map.Overlays.Add(_midpointOverlay);
            map.Overlays.Add(_kfOverlay);
            map.Overlays.Add(_currentOverlay);
            map.Overlays.Add(_kfCurrentOverlay);
            map.Overlays.Add(_sensorOverlay);

            txtMapZoomVal.Text = "MAP ZOOM: " + _zoomValue.ToString(CultureInfo.InvariantCulture);
        }

        private void btnMapZoomPos_Click(object sender, EventArgs e)
        {
            _zoomValue = Math.Min(20, _zoomValue + 1);
            txtMapZoomVal.Text = "MAP ZOOM: " + _zoomValue.ToString(CultureInfo.InvariantCulture);

            map.MaxZoom = _zoomValue;
            map.MinZoom = _zoomValue;
            map.Zoom = _zoomValue;
        }

        private void btnMapZoomNeg_Click(object sender, EventArgs e)
        {
            _zoomValue = Math.Max(2, _zoomValue - 1);
            txtMapZoomVal.Text = "MAP ZOOM: " + _zoomValue.ToString(CultureInfo.InvariantCulture);

            map.MaxZoom = _zoomValue;
            map.MinZoom = _zoomValue;
            map.Zoom = _zoomValue;
        }

        private void StartMapRenderTimer()
        {
            _renderTimer = new System.Windows.Forms.Timer();
            _renderTimer.Interval = RENDER_FPS_INTERVAL_MS;
            _renderTimer.Tick += (s, e) =>
            {
                if (map != null && map.IsHandleCreated && map.Width > 10 && map.Height > 10)
                    map.Invalidate();
            };
            _renderTimer.Start();
        }

        private void StartUiDrainTimer()
        {
            _uiDrainTimer = new System.Windows.Forms.Timer();
            _uiDrainTimer.Interval = UI_DRAIN_INTERVAL_MS;
            _uiDrainTimer.Tick += (s, e) =>
            {
                var sw = Stopwatch.StartNew();
                while (sw.ElapsedMilliseconds < UI_DRAIN_BUDGET_MS)
                {
                    if (!_msgQueue.TryDequeue(out var msg)) break;
                    ApplyMessageOnUi(msg);
                }
            };
            _uiDrainTimer.Start();
        }

        private void StartPredictionTimer()
        {
            _predTimer = new System.Windows.Forms.Timer();
            _predTimer.Interval = PRED_TICK_MS;
            _predTimer.Tick += (s, e) => PredictionTick();
            _predTimer.Start();
        }

        private void PredictionTick()
        {
            if (!KF_ENABLE) return;
            if (_kfById.Count == 0) return;

            DateTime now = DateTime.UtcNow;
            var sw = Stopwatch.StartNew();

            var ids = new List<string>(_kfById.Keys);
            ids.Sort(StringComparer.Ordinal);

            for (int i = 0; i < ids.Count; i++)
            {
                if (sw.ElapsedMilliseconds >= PRED_TICK_BUDGET_MS) break;

                string id = ids[i];

                if (!_activeUntilUtcById.TryGetValue(id, out var until) || now > until)
                    continue;

                if (!_kfById.TryGetValue(id, out var kf)) continue;
                if (!_frameById.TryGetValue(id, out var frame)) continue;

                if (!_predLastWallUtcById.TryGetValue(id, out var lastWall))
                {
                    _predLastWallUtcById[id] = now;
                    _predAccumSecById[id] = 0.0;
                    continue;
                }

                double dtWall = (now - lastWall).TotalSeconds;
                _predLastWallUtcById[id] = now;

                if (dtWall < 0) dtWall = 0;
                if (dtWall > 0.5) dtWall = 0.5;

                double dtData = (MODE == DataMode.SimulationFile) ? (dtWall / Math.Max(1e-6, SIM_TIME_SCALE)) : dtWall;

                double acc = 0.0;
                _predAccumSecById.TryGetValue(id, out acc);
                acc += dtData;

                int steps = 0;
                while (acc >= PRED_STEP_SEC && steps < 6)
                {
                    kf.Predict(PRED_STEP_SEC, KF_ACCEL_SIGMA_MPS2);
                    acc -= PRED_STEP_SEC;
                    steps++;
                }

                _predAccumSecById[id] = acc;

                frame.EnuToLlh(kf.X, kf.Y, 0.0, out double lat, out double lon, out _);
                if (!IsValidLatLon(lat, lon)) continue;

                UpsertKfMarker(id, new PointLatLng(lat, lon), kf);
            }
        }

        private async Task EthernetProducerLoop(CancellationToken ct)
        {
            while (!ct.IsCancellationRequested)
            {
                try
                {
                    using (var client = new TcpClient())
                    {
                        client.NoDelay = true;
                        await client.ConnectAsync(ROBIN_HOST, ROBIN_PORT);

                        using (var stream = client.GetStream())
                        {
                            byte[] buf = new byte[TCP_READ_BUF_BYTES];
                            char[] cbuf = new char[Encoding.UTF8.GetMaxCharCount(buf.Length)];
                            Decoder decoder = Encoding.UTF8.GetDecoder();
                            var sb = new StringBuilder(128 * 1024);

                            while (!ct.IsCancellationRequested)
                            {
                                int n = await stream.ReadAsync(buf, 0, buf.Length, ct);
                                if (n == 0) break;

                                int chars = decoder.GetChars(buf, 0, n, cbuf, 0, false);
                                sb.Append(cbuf, 0, chars);

                                while (TryExtractOneRobin(sb, out string robinXml))
                                {
                                    DateTime arrivalUtc = DateTime.UtcNow;

                                    var msg = new Message
                                    {
                                        ArrivalUtc = arrivalUtc,
                                        FileTsUtc = DateTime.MinValue,
                                        HasGps = TryParseSystemStatusGps(robinXml, out double sLat, out double sLon),
                                        SensorLat = sLat,
                                        SensorLon = sLon,
                                        Tracks = ParseRobinMessage(robinXml)
                                    };

                                    if (msg.Tracks != null)
                                    {
                                        for (int t = 0; t < msg.Tracks.Count; t++)
                                            msg.Tracks[t].TimestampUtc = arrivalUtc;
                                    }

                                    _msgQueue.Enqueue(msg);
                                }
                            }
                        }
                    }
                }
                catch (OperationCanceledException) { return; }
                catch (Exception ex)
                {
                    Debug.WriteLine("Ethernet error: " + ex.Message);
                    try { await Task.Delay(RECONNECT_DELAY_MS, ct); } catch { }
                }
            }
        }

        private async Task SimulationPlaybackLoop(CancellationToken ct)
        {
            while (!ct.IsCancellationRequested)
            {
                if (!File.Exists(SIM_XML_PATH))
                {
                    await Task.Delay(1000, ct);
                    continue;
                }

                string text;
                try { text = File.ReadAllText(SIM_XML_PATH); }
                catch
                {
                    await Task.Delay(1000, ct);
                    continue;
                }

                var robins = ExtractRobinBlocks(text);
                if (robins.Count == 0)
                {
                    await Task.Delay(1000, ct);
                    continue;
                }

                var messages = new List<Message>(robins.Count);

                for (int i = 0; i < robins.Count; i++)
                {
                    if (ct.IsCancellationRequested) return;

                    string robinXml = robins[i];

                    DateTime fileTs = DateTime.MinValue;
                    TryGetMessageTimestampUtc(robinXml, out fileTs);

                    var msg = new Message
                    {
                        ArrivalUtc = DateTime.UtcNow,
                        FileTsUtc = fileTs,
                        HasGps = TryParseSystemStatusGps(robinXml, out double sLat, out double sLon),
                        SensorLat = sLat,
                        SensorLon = sLon,
                        Tracks = ParseRobinMessage(robinXml)
                    };

                    if (msg.Tracks != null && fileTs != DateTime.MinValue)
                    {
                        for (int t = 0; t < msg.Tracks.Count; t++)
                            msg.Tracks[t].TimestampUtc = fileTs;
                    }

                    messages.Add(msg);
                }

                DateTime? prevFileTs = null;

                for (int i = 0; i < messages.Count; i++)
                {
                    if (ct.IsCancellationRequested) return;

                    var m = messages[i];

                    int delayMs = SIM_MIN_DELAY_MS;

                    if (m.FileTsUtc != DateTime.MinValue && prevFileTs.HasValue && prevFileTs.Value != DateTime.MinValue)
                    {
                        double dtMs = (m.FileTsUtc - prevFileTs.Value).TotalMilliseconds;
                        if (dtMs < 0) dtMs = 0;
                        delayMs = Clamp((int)Math.Round(dtMs * SIM_TIME_SCALE), SIM_MIN_DELAY_MS, SIM_MAX_DELAY_MS);
                    }

                    prevFileTs = m.FileTsUtc;

                    SafeInvoke(() => ApplyMessageOnUi(m));
                    await Task.Delay(delayMs, ct);
                }

                if (!SIM_REPEAT)
                {
                    if (!ct.IsCancellationRequested)
                    {
                        SafeInvoke(() => MessageBox.Show(
                            this,
                            "Simulation ended:\n" + Path.GetFileName(SIM_XML_PATH),
                            "Playback Finished",
                            MessageBoxButtons.OK,
                            MessageBoxIcon.Information));
                    }
                    return;
                }

                SafeInvoke(() => ResetAll());
            }
        }

        private void ApplyMessageOnUi(Message msg)
        {
            if (msg == null) return;

            if (msg.HasGps)
                ApplySensorGpsOnUi(msg.SensorLat, msg.SensorLon);

            if (msg.Tracks != null && msg.Tracks.Count > 0)
            {
                DateTime measTime = (MODE == DataMode.SimulationFile && msg.FileTsUtc != DateTime.MinValue)
                    ? msg.FileTsUtc
                    : msg.ArrivalUtc;

                ApplyTracksOnUi(msg.Tracks, measTime);
            }
        }

        private void ApplySensorGpsOnUi(double latDeg, double lonDeg)
        {
            if (!IsValidLatLon(latDeg, lonDeg)) return;

            _sensorLatDeg = latDeg;
            _sensorLonDeg = lonDeg;
            _sensorInit = true;

            var p = new PointLatLng(latDeg, lonDeg);

            if (_sensorMarker == null)
            {
                _sensorMarker = new GMarkerGoogle(p, _robinBmp)
                {
                    ToolTipText = "Robin Radar",
                    ToolTipMode = MarkerTooltipMode.OnMouseOver,
                };
                _sensorOverlay.Markers.Add(_sensorMarker);
                map.Position = p;
            }
            else
            {
                _sensorMarker.Position = p;
            }

            if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(_sensorMarker);
        }

        private void ApplyTracksOnUi(List<TrackSample> updates, DateTime measTimeUtc)
        {
            var accepted = new List<TrackSample>(updates.Count);

            for (int i = 0; i < updates.Count; i++)
            {
                var s = updates[i];
                if (s == null) continue;

                if (!(s.Score >= SCORE_MIN)) continue;
                if (!PassClassFilter(s.Classification)) continue;
                if (!IsValidLatLon(s.LatitudeDeg, s.LongitudeDeg)) continue;

                s.TimestampUtc = measTimeUtc;

                _gridList.Add(s);
                accepted.Add(s);

                if (_gridList.Count > GRID_MAX_ROWS)
                    _gridList.RemoveAt(0);

                _activeUntilUtcById[s.TargetId] = DateTime.UtcNow.AddMilliseconds(ACTIVE_TARGET_TTL_MS);
            }

            DrawMeasured(accepted);

            if (KF_ENABLE)
                ApplyKalmanMeasurementUpdates(accepted, measTimeUtc);
        }

        private void DrawMeasured(List<TrackSample> accepted)
        {
            if (accepted == null || accepted.Count == 0) return;

            for (int i = 0; i < accepted.Count; i++)
            {
                var s = accepted[i];
                if (s == null || string.IsNullOrWhiteSpace(s.TargetId)) continue;

                var cur = new PointLatLng(s.LatitudeDeg, s.LongitudeDeg);

                // تم حذف رسم الميد بوينت
                // if (DRAW_MIDPOINTS && _lastPosByTargetId.TryGetValue(s.TargetId, out var prev))
                // {
                //     ...
                // }

                var measMarker = new GMarkerGoogle(cur, _dotMeasBmp)
                {
                    ToolTipMode = MarkerTooltipMode.OnMouseOver,
                    ToolTipText =
                        "MEAS\nID=" + s.TargetId + "\n" +
                        "Class=" + s.Classification + "\n" +
                        "T=" + s.TimestampUtc.ToString("HH:mm:ss.fff", CultureInfo.InvariantCulture)
                };
                _measuredOverlay.Markers.Add(measMarker);
                if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(measMarker);

                if (DRAW_CURRENT_MARKER)
                    UpsertMeasuredCurrentMarker(s.TargetId, cur, s.TimestampUtc);

                _lastPosByTargetId[s.TargetId] = cur;
            }

            TrimOverlayMarkers(_measuredOverlay, MAP_MAX_MARKERS);
            TrimOverlayMarkers(_midpointOverlay, MAP_MAX_MARKERS);
        }

        private void UpsertMeasuredCurrentMarker(string id, PointLatLng pos, DateTime tsUtc)
        {
            if (_currentOverlay == null) return;

            if (_currentMarkerByTargetId.TryGetValue(id, out var marker))
            {
                marker.Position = pos;
                if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(marker);
                return;
            }

            var m = new GMarkerGoogle(pos, _dotCurrentBmp)
            {
                ToolTipMode = MarkerTooltipMode.OnMouseOver,
                ToolTipText = "MEAS CURRENT\nID=" + id
            };
            _currentMarkerByTargetId[id] = m;
            _currentOverlay.Markers.Add(m);
            if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(m);
        }

        private void ApplyKalmanMeasurementUpdates(List<TrackSample> accepted, DateTime measTimeUtc)
        {
            if (accepted == null || accepted.Count == 0) return;

            for (int i = 0; i < accepted.Count; i++)
            {
                var s = accepted[i];
                if (s == null || string.IsNullOrWhiteSpace(s.TargetId)) continue;

                var frame = GetOrCreateFrame(s.TargetId, s);
                var kf = GetOrCreateKf(s.TargetId, frame, s);

                double alt = (!double.IsNaN(s.AltitudeM) ? s.AltitudeM : 0.0);
                frame.LlhToEnu(s.LatitudeDeg, s.LongitudeDeg, alt, out double zx, out double zy, out _);

                if (KF_USE_MIDPOINT_PSEUDO_MEAS && _kfLastMeasPosById.TryGetValue(s.TargetId, out var prevPos))
                {
                    var mid = GreatCircleMidpoint(prevPos, new PointLatLng(s.LatitudeDeg, s.LongitudeDeg));
                    frame.LlhToEnu(mid.Lat, mid.Lng, alt, out double mx, out double my, out _);
                    kf.Update(mx, my, KF_MEAS_SIGMA_M * KF_MID_SIGMA_MULT);
                }

                kf.Update(zx, zy, KF_MEAS_SIGMA_M);

                if (KF_INJECT_MEAS_VELOCITY)
                {
                    if (_kfLastMeasEnuById.TryGetValue(s.TargetId, out var last) && last.Has)
                    {
                        double dt = (measTimeUtc - last.TimeUtc).TotalSeconds;
                        if (dt > 0.02 && dt < 2.0)
                        {
                            double vx = (zx - last.X) / dt;
                            double vy = (zy - last.Y) / dt;

                            vx = ClampAbs(vx, KF_VEL_CLAMP_MPS);
                            vy = ClampAbs(vy, KF_VEL_CLAMP_MPS);

                            kf.BlendVelocity(vx, vy, KF_VEL_INJECT_BLEND);
                        }
                    }

                    _kfLastMeasEnuById[s.TargetId] = new LastMeasEnu { Has = true, TimeUtc = measTimeUtc, X = zx, Y = zy };
                }

                _kfLastMeasPosById[s.TargetId] = new PointLatLng(s.LatitudeDeg, s.LongitudeDeg);

                frame.EnuToLlh(kf.X, kf.Y, 0.0, out double flat, out double flon, out _);
                s.KfLatDeg = flat;
                s.KfLonDeg = flon;

                double spd = Math.Sqrt(kf.Vx * kf.Vx + kf.Vy * kf.Vy);
                s.KfSpeedMps = spd;

                if (spd > 1e-6)
                {
                    double headingRad = Math.Atan2(kf.Vx, kf.Vy);
                    s.KfHeadingDeg = (headingRad * 180.0 / Math.PI + 360.0) % 360.0;
                }
                else s.KfHeadingDeg = null;

                UpsertKfMarker(s.TargetId, new PointLatLng(flat, flon), kf);

                if (KF_ROUTE_ON_MEASUREMENTS_ONLY)
                    UpsertKfMarkers(s.TargetId, new PointLatLng(flat, flon));
            }
        }

        private void UpsertKfMarker(string id, PointLatLng pos, KalmanCv2D kf)
        {
            if (_kfCurrentOverlay == null) return;

            if (_kfMarkerById.TryGetValue(id, out var marker))
            {
                marker.Position = pos;
                if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(marker);
                return;
            }

            var m = new GMarkerGoogle(pos, _dotKfCurrentBmp)
            {
                ToolTipMode = MarkerTooltipMode.OnMouseOver,
                ToolTipText = "KF CURRENT\nID=" + id
            };
            _kfMarkerById[id] = m;
            _kfCurrentOverlay.Markers.Add(m);
            if (map.IsHandleCreated) map.UpdateMarkerLocalPosition(m);
        }

        private void UpsertKfMarkers(string id, PointLatLng p)
        {
            if (_kfOverlay == null) return;

            if (!_kfMarkersById.TryGetValue(id, out var markers))
            {
                markers = new List<GMarkerGoogle>();
                _kfMarkersById[id] = markers;
            }

            // رسم نقاط الكالمان بدلاً من الخطوط
            var marker = new GMarkerGoogle(p, _dotKfBmp)
            {
                ToolTipText = $"KF {id}",
                ToolTipMode = MarkerTooltipMode.OnMouseOver
            };

            markers.Add(marker);
            _kfOverlay.Markers.Add(marker);

            if (markers.Count > KF_ROUTE_MAX_POINTS)
            {
                int removeCount = markers.Count - KF_ROUTE_MAX_POINTS;
                for (int i = 0; i < removeCount; i++)
                {
                    _kfOverlay.Markers.Remove(markers[i]);
                }
                markers.RemoveRange(0, removeCount);
            }

            if (map.IsHandleCreated)
                map.UpdateMarkerLocalPosition(marker);
        }

        private static void TrimOverlayMarkers(GMapOverlay ov, int max)
        {
            if (ov == null) return;
            if (ov.Markers.Count <= max) return;

            int remove = ov.Markers.Count - max;
            for (int i = 0; i < remove; i++)
                ov.Markers.RemoveAt(0);
        }

        private LocalFrameEnu GetOrCreateFrame(string id, TrackSample s)
        {
            if (_frameById.TryGetValue(id, out var f)) return f;

            double lat0, lon0, h0;

            if (_sensorInit && IsValidLatLon(_sensorLatDeg, _sensorLonDeg))
            {
                lat0 = _sensorLatDeg;
                lon0 = _sensorLonDeg;
                h0 = 0.0;
            }
            else
            {
                lat0 = s.LatitudeDeg;
                lon0 = s.LongitudeDeg;
                h0 = (!double.IsNaN(s.AltitudeM) ? s.AltitudeM : 0.0);
            }

            f = new LocalFrameEnu(lat0, lon0, h0);
            _frameById[id] = f;
            return f;
        }

        private KalmanCv2D GetOrCreateKf(string id, LocalFrameEnu frame, TrackSample s)
        {
            if (_kfById.TryGetValue(id, out var kf)) return kf;

            kf = new KalmanCv2D();

            double alt = (!double.IsNaN(s.AltitudeM) ? s.AltitudeM : 0.0);
            frame.LlhToEnu(s.LatitudeDeg, s.LongitudeDeg, alt, out double x, out double y, out _);
            kf.Initialize(x, y);

            _kfById[id] = kf;
            return kf;
        }

        private static PointLatLng GreatCircleMidpoint(PointLatLng p1, PointLatLng p2)
        {
            double φ1 = ToRad(p1.Lat);
            double λ1 = ToRad(p1.Lng);
            double φ2 = ToRad(p2.Lat);
            double λ2 = ToRad(p2.Lng);

            double dλ = λ2 - λ1;

            double Bx = Math.Cos(φ2) * Math.Cos(dλ);
            double By = Math.Cos(φ2) * Math.Sin(dλ);

            double φ3 = Math.Atan2(
                Math.Sin(φ1) + Math.Sin(φ2),
                Math.Sqrt((Math.Cos(φ1) + Bx) * (Math.Cos(φ1) + Bx) + By * By));

            double λ3 = λ1 + Math.Atan2(By, Math.Cos(φ1) + Bx);
            λ3 = NormalizeLonRad(λ3);

            return new PointLatLng(ToDeg(φ3), ToDeg(λ3));
        }

        private static double NormalizeLonRad(double λ)
        {
            λ = (λ + 3 * Math.PI) % (2 * Math.PI) - Math.PI;
            return λ;
        }

        private static double ToRad(double deg) => deg * (Math.PI / 180.0);
        private static double ToDeg(double rad) => rad * (180.0 / Math.PI);

        private static List<string> ExtractRobinBlocks(string text)
        {
            var list = new List<string>();
            int i = 0;

            while (true)
            {
                int start = text.IndexOf("<Robin", i, StringComparison.OrdinalIgnoreCase);
                if (start < 0) break;

                int end = text.IndexOf("</Robin>", start, StringComparison.OrdinalIgnoreCase);
                if (end < 0) break;

                end += "</Robin>".Length;
                list.Add(text.Substring(start, end - start));
                i = end;
            }

            return list;
        }

        private static bool TryParseToUtc(string s, out DateTime utc)
        {
            utc = DateTime.MinValue;
            if (string.IsNullOrWhiteSpace(s)) return false;

            if (DateTimeOffset.TryParse(
                s.Trim(),
                CultureInfo.InvariantCulture,
                DateTimeStyles.AssumeUniversal | DateTimeStyles.AdjustToUniversal,
                out var dto))
            {
                utc = dto.UtcDateTime;
                return true;
            }

            return false;
        }

        private static bool TryGetMessageTimestampUtc(string robinXml, out DateTime tsUtc)
        {
            tsUtc = DateTime.MinValue;
            try
            {
                var doc = new XmlDocument();
                doc.LoadXml(robinXml);

                var tracks = doc.SelectSingleNode("//Tracks");
                var attr = tracks?.Attributes?["timestamp"]?.Value;
                if (!string.IsNullOrWhiteSpace(attr) && TryParseToUtc(attr, out tsUtc))
                    return true;

                var firstTs = doc.SelectSingleNode("//Track/Timestamp")?.InnerText;
                if (!string.IsNullOrWhiteSpace(firstTs) && TryParseToUtc(firstTs, out tsUtc))
                    return true;
            }
            catch { }
            return false;
        }

        public static List<TrackSample> ParseRobinMessage(string robinXml)
        {
            var list = new List<TrackSample>();
            if (string.IsNullOrWhiteSpace(robinXml)) return list;

            var settings = new XmlReaderSettings
            {
                DtdProcessing = DtdProcessing.Prohibit,
                IgnoreComments = false,
                IgnoreWhitespace = false
            };

            using (var sr = new StringReader(robinXml))
            using (var xr = XmlReader.Create(sr, settings))
            {
                while (xr.Read())
                {
                    if (xr.NodeType != XmlNodeType.Element) continue;
                    if (Eq(xr.LocalName, "Track"))
                    {
                        var t = ReadTrackElement(xr);
                        if (t != null) list.Add(t);
                    }
                }
            }

            return list;
        }

        public static TrackSample ReadTrackElement(XmlReader xr)
        {
            string id = xr.GetAttribute("id");
            if (string.IsNullOrWhiteSpace(id)) return null;

            var t = new TrackSample
            {
                TargetId = id.Trim(),
                TimestampUtc = DateTime.MinValue,
                Classification = "UNKNOWN"
            };

            using (var sub = xr.ReadSubtree())
            {
                sub.Read();
                while (sub.Read())
                {
                    if (sub.NodeType != XmlNodeType.Element) continue;
                    string name = sub.LocalName;

                    if (Eq(name, "Timestamp"))
                    {
                        string s = sub.ReadElementContentAsString();
                        if (!string.IsNullOrWhiteSpace(s) && TryParseToUtc(s, out DateTime utc))
                            t.TimestampUtc = utc;
                    }
                    else if (Eq(name, "Latitude"))
                        t.LatitudeDeg = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Longitude") || Eq(name, "Lon") || Eq(name, "Lng"))
                        t.LongitudeDeg = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Altitude") || Eq(name, "Alt"))
                        t.AltitudeM = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Speed"))
                        t.SpeedMps = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Azimuth"))
                        t.AzimuthDeg = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Elevation"))
                        t.ElevationDeg = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Score"))
                        t.Score = ReadDoubleInvariant(sub);
                    else if (Eq(name, "Classification"))
                        t.Classification = (sub.ReadElementContentAsString() ?? "UNKNOWN").Trim();
                }
            }

            return t;
        }

        public static bool Eq(string a, string b) => string.Equals(a, b, StringComparison.OrdinalIgnoreCase);

        public static bool TryParseDoubleInvariant(string s, out double v)
        {
            v = double.NaN;
            if (string.IsNullOrWhiteSpace(s)) return false;
            s = s.Trim().Replace(',', '.');

            return double.TryParse(
                s,
                NumberStyles.Float | NumberStyles.AllowThousands,
                CultureInfo.InvariantCulture,
                out v);
        }

        public static double ReadDoubleInvariant(XmlReader xr)
        {
            string s = xr.ReadElementContentAsString();
            return TryParseDoubleInvariant(s, out double v) ? v : double.NaN;
        }

        public static bool TryExtractOneRobin(StringBuilder sb, out string robinXml)
        {
            robinXml = null;
            if (sb.Length == 0) return false;

            string s = sb.ToString();

            int start = s.IndexOf("<Robin", StringComparison.OrdinalIgnoreCase);
            if (start < 0)
            {
                if (sb.Length > 1024 * 1024) sb.Clear();
                return false;
            }

            int end = s.IndexOf("</Robin>", start, StringComparison.OrdinalIgnoreCase);
            if (end < 0)
            {
                if (start > 0) sb.Remove(0, start);
                return false;
            }

            end += "</Robin>".Length;

            robinXml = s.Substring(start, end - start);
            sb.Remove(0, end);
            return true;
        }

        public static bool TryParseSystemStatusGps(string robinXml, out double lat, out double lon)
        {
            lat = lon = double.NaN;

            try
            {
                var doc = new XmlDocument();
                doc.LoadXml(robinXml);

                var latNode =
                    doc.SelectSingleNode("//SystemStatus//SensorStatus[Name='GPS']//Position//Latitude") ??
                    doc.SelectSingleNode("//SystemStatus//SensorStatus//Position//Latitude");

                var lonNode =
                    doc.SelectSingleNode("//SystemStatus//SensorStatus[Name='GPS']//Position//Longitude") ??
                    doc.SelectSingleNode("//SystemStatus//SensorStatus//Position//Longitude");

                if (latNode == null || lonNode == null) return false;

                if (!TryParseDoubleInvariant(latNode.InnerText, out lat)) return false;
                if (!TryParseDoubleInvariant(lonNode.InnerText, out lon)) return false;

                return IsValidLatLon(lat, lon);
            }
            catch { return false; }
        }

        public static bool PassClassFilter(string c)
        {
            if (string.IsNullOrWhiteSpace(c)) return false;
            c = c.Trim();

            return c.Equals("DRONE", StringComparison.OrdinalIgnoreCase) ||
                   c.Equals("SUSPECTED_DRONE", StringComparison.OrdinalIgnoreCase) ||
                   c.Equals("FIXED_WING", StringComparison.OrdinalIgnoreCase) ||
                   c.Equals("SUSPECTED_FIXED_WING", StringComparison.OrdinalIgnoreCase);
        }

        public static bool IsValidLatLon(double lat, double lon)
        {
            if (double.IsNaN(lat) || double.IsNaN(lon)) return false;
            if (lat < -90 || lat > 90) return false;
            if (lon < -180 || lon > 180) return false;
            return true;
        }

        private void SafeInvoke(Action a)
        {
            try
            {
                if (IsDisposed || !IsHandleCreated) return;
                if (InvokeRequired) Invoke(a); else a();
            }
            catch { }
        }

        private static int Clamp(int v, int lo, int hi)
        {
            if (v < lo) return lo;
            if (v > hi) return hi;
            return v;
        }

        private static double ClampAbs(double v, double maxAbs)
        {
            if (v > maxAbs) return maxAbs;
            if (v < -maxAbs) return -maxAbs;
            return v;
        }

        private static void SafeDispose(ref Bitmap bmp)
        {
            try { bmp?.Dispose(); } catch { }
            bmp = null;
        }

        private static Bitmap CreateDotBitmap(Color color, int size)
        {
            var bmp = new Bitmap(size, size);
            using (var g = Graphics.FromImage(bmp))
            {
                g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
                g.Clear(Color.Transparent);

                using (var br = new SolidBrush(color))
                    g.FillEllipse(br, 1, 1, size - 2, size - 2);

                using (var pen = new Pen(Color.Black, 1))
                    g.DrawEllipse(pen, 1, 1, size - 2, size - 2);
            }
            return bmp;
        }

        private static Bitmap CreateRingDotBitmap(Color fill, Color border, int size)
        {
            var bmp = new Bitmap(size, size);
            using (var g = Graphics.FromImage(bmp))
            {
                g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
                g.Clear(Color.Transparent);

                using (var pen = new Pen(border, 2))
                    g.DrawEllipse(pen, 2, 2, size - 4, size - 4);

                using (var br = new SolidBrush(fill))
                    g.FillEllipse(br, 4, 4, size - 8, size - 8);
            }
            return bmp;
        }

        private static Bitmap TryLoadSensorBitmap()
        {
            try
            {
                var res = Properties.Resources.iris;
                if (res != null)
                    return new Bitmap(res, new Size(40, 70));
            }
            catch { }

            var bmp = new Bitmap(40, 70);
            using (var g = Graphics.FromImage(bmp))
            {
                g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
                g.Clear(Color.Transparent);
                using (var br = new SolidBrush(Color.CornflowerBlue))
                    g.FillEllipse(br, 4, 4, 32, 32);
                using (var br = new SolidBrush(Color.DarkBlue))
                    g.FillRectangle(br, 18, 30, 4, 34);
                using (var pen = new Pen(Color.Black, 2))
                    g.DrawEllipse(pen, 4, 4, 32, 32);
            }
            return bmp;
        }

        private sealed class LocalFrameEnu
        {
            private const double A = 6378137.0;
            private const double F = 1.0 / 298.257223563;
            private const double E2 = F * (2.0 - F);

            private readonly double _lat0Rad;
            private readonly double _lon0Rad;

            private readonly double _sinLat0;
            private readonly double _cosLat0;
            private readonly double _sinLon0;
            private readonly double _cosLon0;

            private readonly double _x0, _y0, _z0;

            public LocalFrameEnu(double lat0Deg, double lon0Deg, double h0M)
            {
                _lat0Rad = lat0Deg * Math.PI / 180.0;
                _lon0Rad = lon0Deg * Math.PI / 180.0;

                _sinLat0 = Math.Sin(_lat0Rad);
                _cosLat0 = Math.Cos(_lat0Rad);
                _sinLon0 = Math.Sin(_lon0Rad);
                _cosLon0 = Math.Cos(_lon0Rad);

                LlhToEcef(lat0Deg, lon0Deg, h0M, out _x0, out _y0, out _z0);
            }

            public void LlhToEnu(double latDeg, double lonDeg, double hM, out double e, out double n, out double u)
            {
                LlhToEcef(latDeg, lonDeg, hM, out double x, out double y, out double z);
                double dx = x - _x0;
                double dy = y - _y0;
                double dz = z - _z0;

                e = -_sinLon0 * dx + _cosLon0 * dy;
                n = -_sinLat0 * _cosLon0 * dx - _sinLat0 * _sinLon0 * dy + _cosLat0 * dz;
                u = _cosLat0 * _cosLon0 * dx + _cosLat0 * _sinLon0 * dy + _sinLat0 * dz;
            }

            public void EnuToLlh(double e, double n, double u, out double latDeg, out double lonDeg, out double hM)
            {
                double dx = -_sinLon0 * e - _sinLat0 * _cosLon0 * n + _cosLat0 * _cosLon0 * u;
                double dy = _cosLon0 * e - _sinLat0 * _sinLon0 * n + _cosLat0 * _sinLon0 * u;
                double dz = _cosLat0 * n + _sinLat0 * u;

                double x = _x0 + dx;
                double y = _y0 + dy;
                double z = _z0 + dz;

                EcefToLlh(x, y, z, out latDeg, out lonDeg, out hM);
            }

            private static void LlhToEcef(double latDeg, double lonDeg, double hM, out double x, out double y, out double z)
            {
                double lat = latDeg * Math.PI / 180.0;
                double lon = lonDeg * Math.PI / 180.0;

                double sinLat = Math.Sin(lat);
                double cosLat = Math.Cos(lat);
                double sinLon = Math.Sin(lon);
                double cosLon = Math.Cos(lon);

                double N = A / Math.Sqrt(1.0 - E2 * sinLat * sinLat);

                x = (N + hM) * cosLat * cosLon;
                y = (N + hM) * cosLat * sinLon;
                z = (N * (1.0 - E2) + hM) * sinLat;
            }

            private static void EcefToLlh(double x, double y, double z, out double latDeg, out double lonDeg, out double hM)
            {
                double lon = Math.Atan2(y, x);
                double p = Math.Sqrt(x * x + y * y);

                double lat = Math.Atan2(z, p * (1.0 - E2));
                hM = 0.0;

                for (int i = 0; i < 7; i++)
                {
                    double sinLat = Math.Sin(lat);
                    double N = A / Math.Sqrt(1.0 - E2 * sinLat * sinLat);
                    hM = p / Math.Cos(lat) - N;

                    double latNew = Math.Atan2(z, p * (1.0 - E2 * (N / (N + hM))));
                    if (Math.Abs(latNew - lat) < 1e-12) { lat = latNew; break; }
                    lat = latNew;
                }

                latDeg = lat * 180.0 / Math.PI;
                lonDeg = lon * 180.0 / Math.PI;
            }
        }

        // =========================================================
        // 2D CV Kalman filter: [x,vx,y,vy]
        // =========================================================
        private sealed class KalmanCv2D
        {
            private readonly double[] _x = new double[4];
            private readonly double[,] _P = new double[4, 4];

            public double X => _x[0];
            public double Vx => _x[1];
            public double Y => _x[2];
            public double Vy => _x[3];

            public void Initialize(double x, double y)
            {
                _x[0] = x; _x[1] = 0.0;
                _x[2] = y; _x[3] = 0.0;

                ZeroP();
                _P[0, 0] = 25.0;
                _P[2, 2] = 25.0;
                _P[1, 1] = 100.0;
                _P[3, 3] = 100.0;
            }

            public void BlendVelocity(double vxMeas, double vyMeas, double blend01)
            {
                if (blend01 <= 0) return;
                if (blend01 >= 1) { _x[1] = vxMeas; _x[3] = vyMeas; return; }

                _x[1] = _x[1] * (1.0 - blend01) + vxMeas * blend01;
                _x[3] = _x[3] * (1.0 - blend01) + vyMeas * blend01;
            }

            private void ZeroP()
            {
                for (int r = 0; r < 4; r++)
                    for (int c = 0; c < 4; c++)
                        _P[r, c] = 0.0;
            }

            public void Predict(double dt, double accelSigma)
            {
                if (dt <= 0) return;

                _x[0] += _x[1] * dt;
                _x[2] += _x[3] * dt;

                double[,] F = new double[4, 4]
                {
                    {1, dt, 0,  0},
                    {0,  1, 0,  0},
                    {0,  0, 1, dt},
                    {0,  0, 0,  1}
                };

                double q = accelSigma * accelSigma;
                double dt2 = dt * dt;
                double dt3 = dt2 * dt;
                double dt4 = dt2 * dt2;

                double[,] Q = new double[4, 4];
                double q11 = q * (dt4 / 4.0);
                double q12 = q * (dt3 / 2.0);
                double q22 = q * (dt2);

                Q[0, 0] = q11; Q[0, 1] = q12;
                Q[1, 0] = q12; Q[1, 1] = q22;

                Q[2, 2] = q11; Q[2, 3] = q12;
                Q[3, 2] = q12; Q[3, 3] = q22;

                var FP = Mul4x4(F, _P);
                var FPFt = Mul4x4(FP, Transpose4x4(F));

                for (int r = 0; r < 4; r++)
                    for (int c = 0; c < 4; c++)
                        _P[r, c] = FPFt[r, c] + Q[r, c];
            }

            public void Update(double zx, double zy, double measSigma)
            {
                double r = measSigma * measSigma;

                double y0 = zx - _x[0];
                double y1 = zy - _x[2];

                double S00 = _P[0, 0] + r;
                double S01 = _P[0, 2];
                double S10 = _P[2, 0];
                double S11 = _P[2, 2] + r;

                double det = S00 * S11 - S01 * S10;
                if (Math.Abs(det) < 1e-12) return;

                double inv00 = S11 / det;
                double inv01 = -S01 / det;
                double inv10 = -S10 / det;
                double inv11 = S00 / det;

                double p00 = _P[0, 0], p02 = _P[0, 2];
                double p10 = _P[1, 0], p12 = _P[1, 2];
                double p20 = _P[2, 0], p22 = _P[2, 2];
                double p30 = _P[3, 0], p32 = _P[3, 2];

                double k00 = p00 * inv00 + p02 * inv10;
                double k01 = p00 * inv01 + p02 * inv11;

                double k10 = p10 * inv00 + p12 * inv10;
                double k11 = p10 * inv01 + p12 * inv11;

                double k20 = p20 * inv00 + p22 * inv10;
                double k21 = p20 * inv01 + p22 * inv11;

                double k30 = p30 * inv00 + p32 * inv10;
                double k31 = p30 * inv01 + p32 * inv11;

                _x[0] += k00 * y0 + k01 * y1;
                _x[1] += k10 * y0 + k11 * y1;
                _x[2] += k20 * y0 + k21 * y1;
                _x[3] += k30 * y0 + k31 * y1;

                // Simple covariance update: P = (I - K H) P (I - K H)^T
                double[,] I = new double[4, 4];
                for (int i = 0; i < 4; i++) I[i, i] = 1.0;

                I[0, 0] -= k00; I[0, 2] -= k01;
                I[1, 0] -= k10; I[1, 2] -= k11;
                I[2, 0] -= k20; I[2, 2] -= k21;
                I[3, 0] -= k30; I[3, 2] -= k31;

                var newP = Mul4x4(Mul4x4(I, _P), Transpose4x4(I));
                for (int rr = 0; rr < 4; rr++)
                    for (int cc = 0; cc < 4; cc++)
                        _P[rr, cc] = newP[rr, cc];
            }

            private static double[,] Transpose4x4(double[,] M)
            {
                var t = new double[4, 4];
                for (int r = 0; r < 4; r++)
                    for (int c = 0; c < 4; c++)
                        t[c, r] = M[r, c];
                return t;
            }

            private static double[,] Mul4x4(double[,] A, double[,] B)
            {
                var C = new double[4, 4];
                for (int r = 0; r < 4; r++)
                {
                    for (int c = 0; c < 4; c++)
                    {
                        double s = 0.0;
                        for (int k = 0; k < 4; k++)
                            s += A[r, k] * B[k, c];
                        C[r, c] = s;
                    }
                }
                return C;
            }
        }
    }
}
