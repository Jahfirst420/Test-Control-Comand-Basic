#define _WIN32_WINNT 0x0601
#define WIN32_LEAN_AND_MEAN
#define COBJMACROS

#include <windows.h>
#include <windowsx.h>  
#include <wininet.h>
#include <shlwapi.h>   
#include <objidl.h>    
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int    GpStatus;
typedef void   GpGraphics;
typedef void   GpImage;
typedef void   GpBitmap;
typedef void   GpPen;
typedef void   GpBrush;
typedef void   GpSolidFill;
typedef float  REAL;
typedef DWORD  ARGB;
typedef enum { UnitPixelX = 2 } GpUnit;
typedef struct {
    UINT32 GdiplusVersion;
    void  *DebugEventCallback;
    BOOL   SuppressBackgroundThread;
    BOOL   SuppressExternalCodecs;
} GdiplusStartupInput;

GpStatus WINAPI GdiplusStartup(ULONG_PTR*, const GdiplusStartupInput*, void*);
void     WINAPI GdiplusShutdown(ULONG_PTR);
GpStatus WINAPI GdipCreateFromHDC(HDC, GpGraphics**);
GpStatus WINAPI GdipDeleteGraphics(GpGraphics*);
GpStatus WINAPI GdipCreateBitmapFromStream(IStream*, GpBitmap**);
GpStatus WINAPI GdipDisposeImage(GpImage*);
GpStatus WINAPI GdipDrawImageRectI(GpGraphics*, GpImage*, INT, INT, INT, INT);
GpStatus WINAPI GdipCreatePen1(ARGB, REAL, GpUnit, GpPen**);
GpStatus WINAPI GdipDeletePen(GpPen*);
GpStatus WINAPI GdipDrawEllipseI(GpGraphics*, GpPen*, INT, INT, INT, INT);
GpStatus WINAPI GdipDrawLineI(GpGraphics*, GpPen*, INT, INT, INT, INT);
GpStatus WINAPI GdipCreateSolidFill(ARGB, GpSolidFill**);
GpStatus WINAPI GdipDeleteBrush(GpBrush*);
GpStatus WINAPI GdipFillEllipseI(GpGraphics*, GpBrush*, INT, INT, INT, INT);
GpStatus WINAPI GdipSetSmoothingMode(GpGraphics*, int);
#define SMOOTHING_ANTIALIAS 4
#define TILE        256
#define PI          3.14159265358979323846
#define MINZOOM     2
#define MAXZOOM     19
#define WM_TILE_READY (WM_APP + 1)
#define TILE_URL_FMT "https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/%d/%d/%d"
#define TILE_ORDER_ZYX 1
#define HTTP_UA      "MapRadar/1.0 (personal C project; contact set-me@example.com)"
#define MAX_RINGS 16
static double g_rings[MAX_RINGS] = { 5, 10, 25, 50, 100, 250 };
static int    g_nrings = 6;

#define DEFAULT_LAT  51.5074
#define DEFAULT_LON  -0.1278

enum { T_EMPTY = 0, T_REQUESTED, T_BYTES, T_READY, T_FAILED };

typedef struct {
    int   used, z, x, y, status;
    unsigned char *bytes; long nbytes;   
    GpBitmap *bmp;                        
    IStream  *stream;                     
} Tile;

#define CACHE_CAP 16384
#define QUEUE_CAP 8192

static Tile  g_cache[CACHE_CAP];
static int   g_qz[QUEUE_CAP], g_qx[QUEUE_CAP], g_qy[QUEUE_CAP];
static int   g_qhead, g_qtail, g_qcount;
static CRITICAL_SECTION g_lock;    
static HANDLE g_sem;               
static HANDLE g_worker;
static volatile LONG g_running = 1;
static HWND   g_hwnd;
static ULONG_PTR g_gdipToken;
static double g_home_lat = DEFAULT_LAT, g_home_lon = DEFAULT_LON;
static double g_ctr_lat  = DEFAULT_LAT, g_ctr_lon  = DEFAULT_LON;
static int    g_zoom     = 6;
static int    g_hasTarget = 0;
static double g_tgt_lat, g_tgt_lon;
static int    g_dragging = 0, g_pressX, g_pressY, g_lastX, g_lastY, g_moved;
static double g_curLat, g_curLon;   /* under-cursor coords for the HUD */
static int    g_haveCur = 0;

#define ID_EDIT_LAT 101
#define ID_EDIT_LON 102
#define ID_BTN_SET  103
#define ID_EDIT_TLAT 104
#define ID_EDIT_TLON 105
#define ID_BTN_TSET  106
#define ID_EDIT_RINGS 107
#define ID_BTN_RSET   108
static HWND    g_lblHome, g_editLat, g_editLon, g_btnSet;
static HWND    g_lblTgt,  g_editTLat, g_editTLon, g_btnTSet;
static HWND    g_lblRings, g_editRings, g_btnRSet;
static HBRUSH  g_panelBrush;
static WNDPROC g_editOldProc;
static double lon2wx(double lon, int z){
    return (lon + 180.0) / 360.0 * (double)(TILE * (1 << z));
}
static double lat2wy(double lat, int z){
    double s = sin(lat * PI / 180.0);
    double y = 0.5 - log((1 + s) / (1 - s)) / (4 * PI);
    return y * (double)(TILE * (1 << z));
}
static double wx2lon(double wx, int z){
    return wx / (double)(TILE * (1 << z)) * 360.0 - 180.0;
}
static double wy2lat(double wy, int z){
    double n = (double)(TILE * (1 << z));
    return atan(sinh(PI * (1 - 2 * (wy / n)))) * 180.0 / PI;
}
static double meters_per_pixel(double lat, int z){
    return 156543.03392804097 * cos(lat * PI / 180.0) / (double)(1 << z);
}
static double haversine_km(double la1,double lo1,double la2,double lo2){
    double R = 6371.0088;
    double dla = (la2 - la1) * PI / 180.0, dlo = (lo2 - lo1) * PI / 180.0;
    double a = sin(dla/2)*sin(dla/2) +
               cos(la1*PI/180)*cos(la2*PI/180)*sin(dlo/2)*sin(dlo/2);
    return 2 * R * atan2(sqrt(a), sqrt(1 - a));
}
static double bearing_deg(double la1,double lo1,double la2,double lo2){
    double p1 = la1*PI/180, p2 = la2*PI/180, dl = (lo2-lo1)*PI/180;
    double y = sin(dl)*cos(p2);
    double x = cos(p1)*sin(p2) - sin(p1)*cos(p2)*cos(dl);
    double b = atan2(y, x) * 180.0 / PI;
    return fmod(b + 360.0, 360.0);
}
static double clampd(double v,double lo,double hi){ return v<lo?lo:(v>hi?hi:v); }

static unsigned char* http_get(const char *url, long *outlen){
    *outlen = 0;
    HINTERNET hI = InternetOpenA(HTTP_UA, INTERNET_OPEN_TYPE_PRECONFIG, NULL, NULL, 0);
    if(!hI) return NULL;
    HINTERNET hU = InternetOpenUrlA(hI, url, NULL, 0,
                       INTERNET_FLAG_RELOAD | INTERNET_FLAG_NO_UI, 0);
    if(!hU){ InternetCloseHandle(hI); return NULL; }

    size_t cap = 64*1024, len = 0;
    unsigned char *buf = (unsigned char*)malloc(cap);
    if(!buf){ InternetCloseHandle(hU); InternetCloseHandle(hI); return NULL; }

    DWORD got = 0;
    while(InternetReadFile(hU, buf + len, (DWORD)(cap - len), &got) && got > 0){
        len += got;
        if(len + 8192 > cap){
            unsigned char *nb = (unsigned char*)realloc(buf, cap *= 2);
            if(!nb){ free(buf); buf = NULL; break; }
            buf = nb;
        }
    }
    InternetCloseHandle(hU); InternetCloseHandle(hI);
    if(!buf || len == 0){ free(buf); return NULL; }
    *outlen = (long)len;
    return buf;
}

static unsigned tile_hash(int z,int x,int y){
    unsigned h = (unsigned)(z*73856093) ^ (unsigned)(x*19349663) ^ (unsigned)(y*83492791);
    return h % CACHE_CAP;
}
static Tile* cache_find_or_new(int z,int x,int y,int create){
    unsigned i = tile_hash(z,x,y);
    for(int probe = 0; probe < CACHE_CAP; probe++){
        Tile *t = &g_cache[i];
        if(!t->used){
            if(!create) return NULL;
            t->used = 1; t->z = z; t->x = x; t->y = y; t->status = T_EMPTY;
            return t;
        }
        if(t->z==z && t->x==x && t->y==y) return t;
        i = (i + 1) % CACHE_CAP;
    }
    return NULL; 
}
static void enqueue_locked(int z,int x,int y){
    if(g_qcount >= QUEUE_CAP) return;
    g_qz[g_qtail]=z; g_qx[g_qtail]=x; g_qy[g_qtail]=y;
    g_qtail = (g_qtail + 1) % QUEUE_CAP;
    g_qcount++;
    ReleaseSemaphore(g_sem, 1, NULL);
}


static GpBitmap* get_tile(int z,int x,int y){
    GpBitmap *result = NULL;
    EnterCriticalSection(&g_lock);
    Tile *t = cache_find_or_new(z,x,y,1);
    if(t){
        if(t->status == T_EMPTY){
            t->status = T_REQUESTED;
            enqueue_locked(z,x,y);
        } else if(t->status == T_BYTES){
            IStream *s = SHCreateMemStream(t->bytes, (UINT)t->nbytes);
            GpBitmap *bmp = NULL;
            if(s && GdipCreateBitmapFromStream(s, &bmp) == 0 && bmp){
                t->bmp = bmp; t->stream = s; t->status = T_READY;
                result = bmp;
            } else {
                if(s) IStream_Release(s);
                t->status = T_FAILED;
            }
            free(t->bytes); t->bytes = NULL; t->nbytes = 0;
        } else if(t->status == T_READY){
            result = t->bmp;
        }
    }
    LeaveCriticalSection(&g_lock);
    return result;
}

static DWORD WINAPI worker_proc(LPVOID arg){
    (void)arg;
    for(;;){
        WaitForSingleObject(g_sem, INFINITE);
        if(!g_running) break;

        int z,x,y;
        EnterCriticalSection(&g_lock);
        if(g_qcount == 0){ LeaveCriticalSection(&g_lock); continue; }
        z = g_qz[g_qhead]; x = g_qx[g_qhead]; y = g_qy[g_qhead];
        g_qhead = (g_qhead + 1) % QUEUE_CAP; g_qcount--;
        LeaveCriticalSection(&g_lock);

        char url[256];
    #if TILE_ORDER_ZYX
        snprintf(url, sizeof(url), TILE_URL_FMT, z, y, x);
    #else
        snprintf(url, sizeof(url), TILE_URL_FMT, z, x, y);
    #endif
        long len = 0;
        unsigned char *bytes = http_get(url, &len);

        EnterCriticalSection(&g_lock);
        Tile *t = cache_find_or_new(z,x,y,0);
        if(t){
            if(bytes){ t->bytes = bytes; t->nbytes = len; t->status = T_BYTES; }
            else       t->status = T_FAILED;
        } else {
            free(bytes);
        }
        LeaveCriticalSection(&g_lock);

        PostMessage(g_hwnd, WM_TILE_READY, 0, 0);
    }
    return 0;
}


static int ip_geolocate(double *lat, double *lon){
    long len = 0;
    unsigned char *b = http_get("http://ip-api.com/line/?fields=lat,lon", &len);
    if(!b) return 0;
    double la = 0, lo = 0;
    int ok = (sscanf((char*)b, "%lf %lf", &la, &lo) == 2);
    free(b);
    if(ok){ *lat = la; *lon = lo; }
    return ok;
}

static void draw_marker(GpGraphics *g, int cx, int cy, ARGB color){
    GpSolidFill *fill=NULL; GpPen *pen=NULL;
    GdipCreateSolidFill(color, &fill);
    GdipCreatePen1(0xFF000000, 2.0f, UnitPixelX, &pen);
    GdipFillEllipseI(g, (GpBrush*)fill, cx-5, cy-5, 10, 10);
    GdipDrawLineI(g, pen, cx-10, cy, cx+10, cy);
    GdipDrawLineI(g, pen, cx, cy-10, cx, cy+10);
    GdipDeleteBrush((GpBrush*)fill);
    GdipDeletePen(pen);
}

static void paint(HDC winDC, int W, int H){
    
    HDC dc = CreateCompatibleDC(winDC);
    HBITMAP bmp = CreateCompatibleBitmap(winDC, W, H);
    HBITMAP old = (HBITMAP)SelectObject(dc, bmp);

    RECT full = {0,0,W,H};
    HBRUSH bg = CreateSolidBrush(RGB(18,20,26));
    FillRect(dc, &full, bg);
    DeleteObject(bg);

    GpGraphics *g = NULL;
    GdipCreateFromHDC(dc, &g);
    GdipSetSmoothingMode(g, SMOOTHING_ANTIALIAS);

    int z = g_zoom, n = 1 << z;
    double cwx = lon2wx(g_ctr_lon, z), cwy = lat2wy(g_ctr_lat, z);
    double left = cwx - W/2.0, top = cwy - H/2.0;

    int tx0 = (int)floor(left / TILE), ty0 = (int)floor(top / TILE);
    int tx1 = (int)floor((left + W) / TILE), ty1 = (int)floor((top + H) / TILE);
    for(int ty = ty0; ty <= ty1; ty++){
        if(ty < 0 || ty >= n) continue;
        for(int tx = tx0; tx <= tx1; tx++){
            int wx = ((tx % n) + n) % n;               
            int sx = (int)lround(tx * (double)TILE - left);
            int sy = (int)lround(ty * (double)TILE - top);
            GpBitmap *b = get_tile(z, wx, ty);
            if(b) GdipDrawImageRectI(g, b, sx, sy, TILE, TILE);
        }
    }

    
    double hx = lon2wx(g_home_lon, z) - left;
    double hy = lat2wy(g_home_lat, z) - top;
    double mpp = meters_per_pixel(g_home_lat, z);

    GpPen *ring=NULL, *spoke=NULL;
    GdipCreatePen1(0x6600FFEE, 1.5f, UnitPixelX, &ring);   
    GdipCreatePen1(0x3300FFEE, 1.0f, UnitPixelX, &spoke);
    for(int r = 0; r < g_nrings; r++){
        int px = (int)lround(g_rings[r] * 1000.0 / mpp);
        if(px < 4 || px > 8000) continue;
        GdipDrawEllipseI(g, ring, (int)hx - px, (int)hy - px, px*2, px*2);
    }
    
    double maxpx = g_rings[g_nrings-1] * 1000.0 / mpp;
    if(maxpx > 4000) maxpx = 4000;
    for(int a = 0; a < 360; a += 45){
        double rad = a * PI / 180.0;
        int ex = (int)lround(hx + sin(rad) * maxpx);
        int ey = (int)lround(hy - cos(rad) * maxpx);
        GdipDrawLineI(g, spoke, (int)hx, (int)hy, ex, ey);
    }
    GdipDeletePen(ring); GdipDeletePen(spoke);

    draw_marker(g, (int)lround(hx), (int)lround(hy), 0xFF33FF66); /* lime */

    if(g_hasTarget){
        double txp = lon2wx(g_tgt_lon, z) - left;
        double typ = lat2wy(g_tgt_lat, z) - top;
        GpPen *line=NULL;
        GdipCreatePen1(0xCCFF3333, 2.0f, UnitPixelX, &line);   /* red */
        GdipDrawLineI(g, line, (int)hx, (int)hy, (int)txp, (int)typ);
        GdipDeletePen(line);
        draw_marker(g, (int)lround(txp), (int)lround(typ), 0xFFFF3333);
    }

    GdipDeleteGraphics(g);   

    SetBkMode(dc, TRANSPARENT);
    HFONT font = CreateFontA(-14,0,0,0,FW_SEMIBOLD,0,0,0,DEFAULT_CHARSET,
                 OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,
                 FF_MODERN,"Consolas");
    HFONT oldf = (HFONT)SelectObject(dc, font);

    char buf[256];
    int y = 10;
    #define LINE(color, ...) do{ \
        SetTextColor(dc, RGB(0,0,0)); snprintf(buf,sizeof(buf),__VA_ARGS__); \
        TextOutA(dc, 13, y+1, buf, (int)strlen(buf)); \
        SetTextColor(dc, color);     TextOutA(dc, 12, y, buf, (int)strlen(buf)); \
        y += 18; }while(0)

    LINE(RGB(120,220,255), "MAP RADAR  -  C2-style demo");
    LINE(RGB(230,230,230), "Zoom %d   HOME %.5f, %.5f", z, g_home_lat, g_home_lon);
    if(g_haveCur)
        LINE(RGB(200,200,200), "Cursor %.5f, %.5f   %.2f km from HOME",
             g_curLat, g_curLon, haversine_km(g_home_lat,g_home_lon,g_curLat,g_curLon));
    if(g_hasTarget){
        double d = haversine_km(g_home_lat,g_home_lon,g_tgt_lat,g_tgt_lon);
        double br = bearing_deg(g_home_lat,g_home_lon,g_tgt_lat,g_tgt_lon);
        LINE(RGB(255,120,120), "TARGET %.5f, %.5f", g_tgt_lat, g_tgt_lon);
        LINE(RGB(255,180,120), "DISTANCE %.3f km   BEARING %.1f deg", d, br);
    }

    SetTextColor(dc, RGB(120,240,220));
    for(int r = 0; r < g_nrings; r++){
        int px = (int)lround(g_rings[r] * 1000.0 / mpp);
        if(px < 12 || px > 8000) continue;
        snprintf(buf,sizeof(buf), "%g km", g_rings[r]);
        TextOutA(dc, (int)hx + 4, (int)hy - px, buf, (int)strlen(buf));
    }

    SetTextColor(dc, RGB(150,150,160));
    const char *help = "Drag pan  |  Wheel/+/- zoom  |  Click set TARGET  |  "
                       "RClick clear  |  H set HOME here  |  G geolocate";
    TextOutA(dc, 12, H - 22, help, (int)strlen(help));

    SelectObject(dc, oldf); DeleteObject(font);
    #undef LINE

    BitBlt(winDC, 0, 0, W, H, dc, 0, 0, SRCCOPY);
    SelectObject(dc, old);
    DeleteObject(bmp);
    DeleteDC(dc);
}

static void screen_to_geo(int px,int py,int W,int H,double *lat,double *lon){
    double cwx = lon2wx(g_ctr_lon, g_zoom), cwy = lat2wy(g_ctr_lat, g_zoom);
    double left = cwx - W/2.0, top = cwy - H/2.0;
    *lon = wx2lon(left + px, g_zoom);
    *lat = wy2lat(top  + py, g_zoom);
}

static void do_zoom(int delta,int mx,int my,int W,int H){
    double glat, glon;
    screen_to_geo(mx, my, W, H, &glat, &glon);      
    int nz = g_zoom + delta;
    if(nz < MINZOOM) nz = MINZOOM;
    if(nz > MAXZOOM) nz = MAXZOOM;
    if(nz == g_zoom) return;
    g_zoom = nz;

    double nwx = lon2wx(glon, g_zoom), nwy = lat2wy(glat, g_zoom);
    double ncwx = nwx - mx + W/2.0, ncwy = nwy - my + H/2.0;
    g_ctr_lon = wx2lon(ncwx, g_zoom);
    g_ctr_lat = clampd(wy2lat(ncwy, g_zoom), -85.05, 85.05);
}

static void layout_controls(int W, int H){
    (void)H;
    int panelW = 300, bx = W - panelW - 12;
    if(bx < 12) bx = 12;
    int y = 10;
    MoveWindow(g_lblHome, bx,      y,    panelW, 18, TRUE); y += 20;
    MoveWindow(g_editLat, bx,      y,    145,    24, TRUE);
    MoveWindow(g_editLon, bx+155,  y,    145,    24, TRUE); y += 28;
    MoveWindow(g_btnSet,  bx,      y,    panelW, 24, TRUE); y += 34;
    MoveWindow(g_lblTgt,  bx,      y,    panelW, 18, TRUE); y += 20;
    MoveWindow(g_editTLat,bx,      y,    145,    24, TRUE);
    MoveWindow(g_editTLon,bx+155,  y,    145,    24, TRUE); y += 28;
    MoveWindow(g_btnTSet, bx,      y,    panelW, 24, TRUE); y += 34;
    MoveWindow(g_lblRings,bx,      y,    panelW, 18, TRUE); y += 20;
    MoveWindow(g_editRings,bx,     y,    panelW, 24, TRUE); y += 28;
    MoveWindow(g_btnRSet, bx,      y,    panelW, 24, TRUE);
}
static void update_home_fields(void){
    char b[64];
    snprintf(b,sizeof(b), "%.5f", g_home_lat); SetWindowTextA(g_editLat, b);
    snprintf(b,sizeof(b), "%.5f", g_home_lon); SetWindowTextA(g_editLon, b);
}
static void update_target_fields(void){
    char b[64];
    if(g_hasTarget){
        snprintf(b,sizeof(b), "%.5f", g_tgt_lat); SetWindowTextA(g_editTLat, b);
        snprintf(b,sizeof(b), "%.5f", g_tgt_lon); SetWindowTextA(g_editTLon, b);
    }
}
static void update_rings_field(void){
    char b[256]; int p = 0;
    for(int i = 0; i < g_nrings; i++)
        p += snprintf(b+p, sizeof(b)-p, (i? ", %g" : "%g"), g_rings[i]);
    SetWindowTextA(g_editRings, b);
}
static void apply_home_from_fields(HWND hwnd){
    char la[64], lo[64]; double a, o;
    GetWindowTextA(g_editLat, la, sizeof(la));
    GetWindowTextA(g_editLon, lo, sizeof(lo));
    if(sscanf(la, "%lf", &a) == 1 && sscanf(lo, "%lf", &o) == 1 &&
       a >= -85.05 && a <= 85.05 && o >= -180.0 && o <= 180.0){
        g_home_lat = g_ctr_lat = a;
        g_home_lon = g_ctr_lon = o;
        update_home_fields();
        SetFocus(hwnd);
        InvalidateRect(hwnd, NULL, FALSE);
    } else {
        MessageBoxA(hwnd,
            "Invalid coordinates.\nLatitude -85..85, longitude -180..180.",
            "Set HOME", MB_OK | MB_ICONWARNING);
    }
}
static void apply_target_from_fields(HWND hwnd){
    char la[64], lo[64]; double a, o;
    GetWindowTextA(g_editTLat, la, sizeof(la));
    GetWindowTextA(g_editTLon, lo, sizeof(lo));
    if(sscanf(la, "%lf", &a) == 1 && sscanf(lo, "%lf", &o) == 1 &&
       a >= -85.05 && a <= 85.05 && o >= -180.0 && o <= 180.0){
        g_tgt_lat = a; g_tgt_lon = o; g_hasTarget = 1;
        g_ctr_lat = a; g_ctr_lon = o; 
        SetFocus(hwnd);
        InvalidateRect(hwnd, NULL, FALSE);
    } else {
        MessageBoxA(hwnd,
            "Invalid coordinates.\nLatitude -85..85, longitude -180..180.",
            "Set TARGET", MB_OK | MB_ICONWARNING);
    }
}
static void apply_rings_from_field(HWND hwnd){
    char txt[256]; GetWindowTextA(g_editRings, txt, sizeof(txt));
    double tmp[MAX_RINGS]; int cnt = 0;
    for(char *p = txt; *p && cnt < MAX_RINGS; ){
        while(*p==' '||*p==','||*p=='\t') p++; 
        if(!*p) break;
        char *end; double v = strtod(p, &end);
        if(end == p){ p++; continue; } 
        if(v > 0) tmp[cnt++] = v;
        p = end;
    }
    if(cnt == 0){
        MessageBoxA(hwnd, "Enter one or more positive numbers,\ne.g.  5, 10, 25, 50, 100",
                    "Set rings", MB_OK | MB_ICONWARNING);
        return;
    }
    for(int i = 0; i < cnt; i++) g_rings[i] = tmp[i];
    g_nrings = cnt;
    update_rings_field(); 
    SetFocus(hwnd);
    InvalidateRect(hwnd, NULL, FALSE);
}
static LRESULT CALLBACK EditProc(HWND h, UINT m, WPARAM w, LPARAM l){
    if(m == WM_KEYDOWN && w == VK_RETURN){
        int id = GetDlgCtrlID(h);
        HWND parent = GetParent(h);
        if(id == ID_EDIT_TLAT || id == ID_EDIT_TLON)
            SendMessage(parent, WM_COMMAND, MAKEWPARAM(ID_BTN_TSET, BN_CLICKED), 0);
        else if(id == ID_EDIT_RINGS)
            SendMessage(parent, WM_COMMAND, MAKEWPARAM(ID_BTN_RSET, BN_CLICKED), 0);
        else
            SendMessage(parent, WM_COMMAND, MAKEWPARAM(ID_BTN_SET, BN_CLICKED), 0);
        return 0;
    }
    return CallWindowProc(g_editOldProc, h, m, w, l);
}

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp){
    RECT rc; GetClientRect(hwnd, &rc);
    int W = rc.right, H = rc.bottom;

    switch(msg){
    case WM_CREATE: {
        HINSTANCE hi = ((LPCREATESTRUCT)lp)->hInstance;
        HFONT gf = (HFONT)GetStockObject(DEFAULT_GUI_FONT);
        g_panelBrush = CreateSolidBrush(RGB(24,26,32));
        g_lblHome = CreateWindowExA(0,"STATIC","Set HOME  (lat , lon):",
                        WS_CHILD|WS_VISIBLE, 0,0,10,10, hwnd, NULL, hi, NULL);
        g_editLat = CreateWindowExA(WS_EX_CLIENTEDGE,"EDIT","",
                        WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL, 0,0,10,10,
                        hwnd,(HMENU)ID_EDIT_LAT, hi, NULL);
        g_editLon = CreateWindowExA(WS_EX_CLIENTEDGE,"EDIT","",
                        WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL, 0,0,10,10,
                        hwnd,(HMENU)ID_EDIT_LON, hi, NULL);
        g_btnSet  = CreateWindowExA(0,"BUTTON","Set HOME  (or Enter)",
                        WS_CHILD|WS_VISIBLE|BS_PUSHBUTTON, 0,0,10,10,
                        hwnd,(HMENU)ID_BTN_SET, hi, NULL);
        g_lblTgt  = CreateWindowExA(0,"STATIC","Set TARGET  (lat , lon):",
                        WS_CHILD|WS_VISIBLE, 0,0,10,10, hwnd, NULL, hi, NULL);
        g_editTLat= CreateWindowExA(WS_EX_CLIENTEDGE,"EDIT","",
                        WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL, 0,0,10,10,
                        hwnd,(HMENU)ID_EDIT_TLAT, hi, NULL);
        g_editTLon= CreateWindowExA(WS_EX_CLIENTEDGE,"EDIT","",
                        WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL, 0,0,10,10,
                        hwnd,(HMENU)ID_EDIT_TLON, hi, NULL);
        g_btnTSet = CreateWindowExA(0,"BUTTON","Set TARGET  (or Enter)",
                        WS_CHILD|WS_VISIBLE|BS_PUSHBUTTON, 0,0,10,10,
                        hwnd,(HMENU)ID_BTN_TSET, hi, NULL);
        g_lblRings= CreateWindowExA(0,"STATIC","Range rings, km  (comma list):",
                        WS_CHILD|WS_VISIBLE, 0,0,10,10, hwnd, NULL, hi, NULL);
        g_editRings=CreateWindowExA(WS_EX_CLIENTEDGE,"EDIT","",
                        WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL, 0,0,10,10,
                        hwnd,(HMENU)ID_EDIT_RINGS, hi, NULL);
        g_btnRSet = CreateWindowExA(0,"BUTTON","Apply rings  (or Enter)",
                        WS_CHILD|WS_VISIBLE|BS_PUSHBUTTON, 0,0,10,10,
                        hwnd,(HMENU)ID_BTN_RSET, hi, NULL);
        SendMessage(g_lblHome, WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_editLat, WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_editLon, WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_btnSet,  WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_lblTgt,  WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_editTLat,WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_editTLon,WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_btnTSet, WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_lblRings,WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_editRings,WM_SETFONT,(WPARAM)gf,TRUE);
        SendMessage(g_btnRSet, WM_SETFONT,(WPARAM)gf,TRUE);
        g_editOldProc = (WNDPROC)SetWindowLongPtr(g_editLat, GWLP_WNDPROC,(LONG_PTR)EditProc);
        SetWindowLongPtr(g_editLon,  GWLP_WNDPROC,(LONG_PTR)EditProc);
        SetWindowLongPtr(g_editTLat, GWLP_WNDPROC,(LONG_PTR)EditProc);
        SetWindowLongPtr(g_editTLon, GWLP_WNDPROC,(LONG_PTR)EditProc);
        SetWindowLongPtr(g_editRings,GWLP_WNDPROC,(LONG_PTR)EditProc);
        layout_controls(W, H);
        update_home_fields();
        update_rings_field();
        return 0;
    }

    case WM_SIZE:
        layout_controls(W, H);
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;

    case WM_COMMAND:
        switch(LOWORD(wp)){
        case ID_BTN_SET:  apply_home_from_fields(hwnd);   break;
        case ID_BTN_TSET: apply_target_from_fields(hwnd); break;
        case ID_BTN_RSET: apply_rings_from_field(hwnd);   break;
        }
        return 0;

    case WM_CTLCOLORSTATIC:
        SetTextColor((HDC)wp, RGB(230,230,235));
        SetBkColor((HDC)wp, RGB(24,26,32));
        return (LRESULT)g_panelBrush;

    case WM_ERASEBKGND: return 1; 

    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(hwnd, &ps);
        paint(dc, W, H);
        EndPaint(hwnd, &ps);
        return 0;
    }

    case WM_TILE_READY:
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;

    case WM_LBUTTONDOWN:
        SetCapture(hwnd);
        g_dragging = 1; g_moved = 0;
        g_pressX = g_lastX = GET_X_LPARAM(lp);
        g_pressY = g_lastY = GET_Y_LPARAM(lp);
        return 0;

    case WM_MOUSEMOVE: {
        int mx = GET_X_LPARAM(lp), my = GET_Y_LPARAM(lp);
        screen_to_geo(mx, my, W, H, &g_curLat, &g_curLon);
        g_haveCur = 1;
        if(g_dragging){
            int dx = mx - g_lastX, dy = my - g_lastY;
            if(abs(mx-g_pressX)+abs(my-g_pressY) > 3) g_moved = 1;
            double cwx = lon2wx(g_ctr_lon, g_zoom) - dx;
            double cwy = lat2wy(g_ctr_lat, g_zoom) - dy;
            g_ctr_lon = wx2lon(cwx, g_zoom);
            g_ctr_lat = clampd(wy2lat(cwy, g_zoom), -85.05, 85.05);
            g_lastX = mx; g_lastY = my;
        }
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;
    }

    case WM_LBUTTONUP: {
        if(g_dragging && !g_moved){
            int mx = GET_X_LPARAM(lp), my = GET_Y_LPARAM(lp);
            screen_to_geo(mx, my, W, H, &g_tgt_lat, &g_tgt_lon);
            g_hasTarget = 1;
            update_target_fields();
        }
        g_dragging = 0; ReleaseCapture();
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;
    }

    case WM_RBUTTONUP:
        g_hasTarget = 0;
        SetWindowTextA(g_editTLat, ""); SetWindowTextA(g_editTLon, "");
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;

    case WM_MOUSEWHEEL: {
        POINT p = { GET_X_LPARAM(lp), GET_Y_LPARAM(lp) };
        ScreenToClient(hwnd, &p);
        do_zoom(GET_WHEEL_DELTA_WPARAM(wp) > 0 ? 1 : -1, p.x, p.y, W, H);
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;
    }

    case WM_KEYDOWN:
        switch(wp){
        case VK_ADD: case VK_OEM_PLUS: do_zoom(+1, W/2, H/2, W, H); break;
        case VK_SUBTRACT: case VK_OEM_MINUS: do_zoom(-1, W/2, H/2, W, H); break;
        case VK_LEFT:  g_ctr_lon = wx2lon(lon2wx(g_ctr_lon,g_zoom)-80, g_zoom); break;
        case VK_RIGHT: g_ctr_lon = wx2lon(lon2wx(g_ctr_lon,g_zoom)+80, g_zoom); break;
        case VK_UP:    g_ctr_lat = clampd(wy2lat(lat2wy(g_ctr_lat,g_zoom)-80,g_zoom),-85.05,85.05); break;
        case VK_DOWN:  g_ctr_lat = clampd(wy2lat(lat2wy(g_ctr_lat,g_zoom)+80,g_zoom),-85.05,85.05); break;
        case 'H': g_home_lat = g_ctr_lat; g_home_lon = g_ctr_lon; update_home_fields(); break;
        case 'G': {
            double la, lo;
            if(ip_geolocate(&la,&lo)){
                g_home_lat = g_ctr_lat = la;
                g_home_lon = g_ctr_lon = lo;
                g_zoom = 11;
                update_home_fields();
            }
            break;
        }
        case VK_ESCAPE: DestroyWindow(hwnd); break;
        }
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;

    case WM_DESTROY:
        InterlockedExchange(&g_running, 0);
        ReleaseSemaphore(g_sem, 1, NULL);
        if(g_panelBrush) DeleteObject(g_panelBrush);
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcA(hwnd, msg, wp, lp);
}

int WINAPI WinMain(HINSTANCE hInst, HINSTANCE prev, LPSTR cmd, int show){
    (void)prev; (void)cmd;

    GdiplusStartupInput gsi = {0}; gsi.GdiplusVersion = 1;
    GdiplusStartup(&g_gdipToken, &gsi, NULL);

    InitializeCriticalSection(&g_lock);
    g_sem = CreateSemaphoreA(NULL, 0, QUEUE_CAP, NULL);

    double la, lo;
    if(ip_geolocate(&la, &lo)){
        g_home_lat = g_ctr_lat = la;
        g_home_lon = g_ctr_lon = lo;
        g_zoom = 11;
    }

    g_worker = CreateThread(NULL, 0, worker_proc, NULL, 0, NULL);

    WNDCLASSA wc = {0};
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hInst;
    wc.hCursor       = LoadCursor(NULL, IDC_ARROW);
    wc.lpszClassName = "MapRadarWnd";
    RegisterClassA(&wc);

    g_hwnd = CreateWindowA("MapRadarWnd", "Map Radar - C2-style demo",
                WS_OVERLAPPEDWINDOW | WS_CLIPCHILDREN,
                CW_USEDEFAULT, CW_USEDEFAULT, 1100, 760,
                NULL, NULL, hInst, NULL);
    ShowWindow(g_hwnd, show);
    UpdateWindow(g_hwnd);

    MSG m;
    while(GetMessage(&m, NULL, 0, 0) > 0){
        TranslateMessage(&m);
        DispatchMessage(&m);
    }

    WaitForSingleObject(g_worker, 2000);
    for(int i = 0; i < CACHE_CAP; i++){
        if(g_cache[i].bmp)    GdipDisposeImage(g_cache[i].bmp);
        if(g_cache[i].stream) IStream_Release(g_cache[i].stream);
        if(g_cache[i].bytes)  free(g_cache[i].bytes);
    }
    DeleteCriticalSection(&g_lock);
    GdiplusShutdown(g_gdipToken);
    return 0;
}
