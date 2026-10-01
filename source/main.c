#include <3ds.h>
#include <citro2d.h>
#include <dirent.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DATA_ROOT "sdmc:/3ds/3DSBible/data/"
#define SAVE_FILE "sdmc:/3ds/3DSBible/last.txt"

#define MAXBOOKS 70
#define MAXVERS  16
#define MAXITEMS 6000
#define MAXPAGES 200
#define GLYPHS   20000

#define BODY_SC  0.55f
#define NUM_SC   0.36f
#define PAGE_W   320
#define PAD_X    22
#define TEXT_W   (PAGE_W - 2 * PAD_X)
#define TEXT_TOP 36
#define TEXT_BOT 204
#define HEADER_H 62
#define ANIM_FRAMES 12 

#define Z_BG   0.0f
#define Z_PAGE 0.1f
#define Z_SHADE 0.2f
#define Z_RULE 0.3f
#define Z_TEXT 0.5f
#define Z_HDR  0.7f
#define Z_HDR_TEXT 0.9f
#define Z_BAR  0.95f
#define Z_BAR_TEXT 0.98f

#define CLR_PARCH   C2D_Color32(0xF3, 0xE8, 0xCB, 0xFF)
#define CLR_PARCH_D C2D_Color32(0xE2, 0xD0, 0xA8, 0xFF)
#define CLR_RULE    C2D_Color32(0xC9, 0xB4, 0x88, 0xFF)
#define CLR_INK     C2D_Color32(0x2B, 0x1D, 0x12, 0xFF)
#define CLR_RED     C2D_Color32(0x8B, 0x1E, 0x1E, 0xFF)
#define CLR_LEATHER C2D_Color32(0x3B, 0x1F, 0x14, 0xFF)
#define CLR_GOLD    C2D_Color32(0xD2, 0xAA, 0x52, 0xFF)
#define CLR_ARROW   C2D_Color32(0xB8, 0x92, 0x45, 0xB0)
#define SH_CLEAR    C2D_Color32(0x40, 0x25, 0x10, 0x00)
#define SH_EDGE     C2D_Color32(0x40, 0x25, 0x10, 0x3C)
#define SH_SPINE    C2D_Color32(0x40, 0x25, 0x10, 0x8C)

#define LIST_TOP 28
#define ROWH     24
#define GRID_COLS 6
#define CELL_W   50
#define CELL_H   40
#define GRID_X   10
#define GRID_TOP 32

#define BTN_Y 213
#define BTN_H 22
#define BTN_W 56
#define BTN_GAP 6
#define BTN_COUNT 5

typedef struct {
    char file[64];
    char name[48];
    int chapters;
} Book;

typedef struct {
    char id[48];
    char name[64];
    char cover[64];
    char chap[24];
} Version;

typedef struct {
    C2D_Text t;
    float x, y, sc;
    u32 clr;
} Item;

typedef struct { bool active, moved; int sx, sy, ly; } Drag;

enum { ST_BOOKS, ST_CHAPTERS, ST_READ, ST_VERSIONS };

static Book books[MAXBOOKS];
static int nbooks = 0;

static Version versions[MAXVERS];
static int nversions = 0;
static int curVer = 0;
static char dataDir[320] = DATA_ROOT;

static Item items[MAXITEMS];
static int nitems = 0;
static int pageStart[MAXPAGES + 2];
static int pageCount = 1;

static C2D_TextBuf dynBuf, pageBuf;
static C3D_RenderTarget *topT, *botT;

static float lh = 18.0f, spaceW = 4.0f;
static float curX = 0;
static int curLine = 0, curPage = 0;

static int state = ST_BOOKS;
static int verPrev = ST_BOOKS;
static int curBook = -1, curChapter = 1, spread = 0;
static int bookCur = 0, chapCur = 0, verCur = 0;
static float bookScroll = 0, chapScroll = 0, verScroll = 0;
static Drag drag;
static int navRep = 0;


static bool animOn = false;
static int animDir = 0;
static int animFrom = 0;
static int animFrame = 0;

static float xs = 1.0f, xp = 0.0f, zb = 0.0f, zm = 1.0f;
#define TX(x) (xp + ((x) - xp) * xs)
#define ZZ(z) (zb + (z) * zm)

static void R(float x, float y, float z, float w, float h, u32 c) {
    C2D_DrawRectSolid(TX(x), y, ZZ(z), w * xs, h, c);
}

static void RG(float x, float y, float z, float w, float h, u32 tl, u32 tr, u32 bl, u32 br) {
    C2D_DrawRectangle(TX(x), y, ZZ(z), w * xs, h, tl, tr, bl, br);
}

static void TRI(float x0, float y0, float x1, float y1, float x2, float y2, u32 c, float z) {
    C2D_DrawTriangle(TX(x0), y0, c, TX(x1), y1, c, TX(x2), y2, c, ZZ(z));
}

static void drawText(const char *s, float x, float y, float sc, u32 clr, int align, float z) {
    C2D_Text t;
    if (!C2D_TextParse(&t, dynBuf, s)) return;
    C2D_TextOptimize(&t);
    float w, h;
    C2D_TextGetDimensions(&t, sc * xs, sc, &w, &h);
    float X = TX(x);
    if (align == 1) X -= w / 2;
    else if (align == 2) X -= w;
    C2D_DrawText(&t, C2D_WithColor, X, y, ZZ(z), sc * xs, sc, clr);
}

// Shrinks a text scale so the string fits within maxW pixels
static float fitScale(const char *s, float sc, float maxW) {
    C2D_Text t;
    if (!C2D_TextParse(&t, dynBuf, s)) return sc;
    float w, h;
    C2D_TextGetDimensions(&t, sc, sc, &w, &h);
    return w > maxW ? sc * maxW / w : sc;
}

static void frameRect(float x, float y, float w, float h, float t, u32 c, float z) {
    R(x, y, z, w, t, c);
    R(x, y + h - t, z, w, t, c);
    R(x, y, z, t, h, c);
    R(x + w - t, y, z, t, h, c);
}

static void ornament(float cx, float y, float halfW, u32 c, float z) {
    R(cx - halfW, y, z, halfW - 9, 1, c);
    R(cx + 9, y, z, halfW - 9, 1, c);
    TRI(cx - 6, y, cx, y - 4, cx + 6, y, c, z);
    TRI(cx - 6, y, cx, y + 4, cx + 6, y, c, z);
}

static float clampf(float v, float lo, float hi) { return v < lo ? lo : (v > hi ? hi : v); }

static void ensureVisible(float *scroll, float itemTop, float itemH, float viewH) {
    if (itemTop < *scroll) *scroll = itemTop;
    if (itemTop + itemH > *scroll + viewH) *scroll = itemTop + itemH - viewH;
}

static u32 navKeys(u32 kDown, u32 kHeld) {
    u32 mask = KEY_DUP | KEY_DDOWN | KEY_DLEFT | KEY_DRIGHT;
    u32 fire = kDown & mask;
    if (kHeld & mask) {
        navRep++;
        if (navRep > 18 && navRep % 4 == 0) fire |= (kHeld & mask);
    } else navRep = 0;
    return fire;
}

// Touch drag-to-scroll
static bool dragUpdate(u32 kDown, u32 kHeld, u32 kUp, touchPosition tp, float *scroll, int *tx, int *ty) {
    bool tapped = false;
    if (kDown & KEY_TOUCH) {
        drag.active = true; drag.moved = false;
        drag.sx = tp.px; drag.sy = tp.py; drag.ly = tp.py;
    } else if ((kHeld & KEY_TOUCH) && drag.active) {
        if (abs(tp.py - drag.sy) > 6) drag.moved = true;
        if (drag.moved) *scroll -= (float)(tp.py - drag.ly);
        drag.ly = tp.py;
    }
    if ((kUp & KEY_TOUCH) && drag.active) {
        drag.active = false;
        if (!drag.moved) { *tx = drag.sx; *ty = drag.sy; tapped = true; }
    }
    return tapped;
}

static void versionDir(const Version *v, char *out, size_t n) {
    if (v->id[0]) snprintf(out, n, DATA_ROOT "%s/", v->id);
    else snprintf(out, n, "%s", DATA_ROOT);
}

static void readLine(FILE *f, char *dst, size_t n) {
    char buf[256];
    if (!fgets(buf, sizeof buf, f)) return;
    buf[strcspn(buf, "\r\n")] = 0;
    if (buf[0]) snprintf(dst, n, "%s", buf);
}

// info.txt
static void readInfo(Version *v) {
    snprintf(v->name, sizeof v->name, "%s", v->id[0] ? v->id : "Bible");
    snprintf(v->cover, sizeof v->cover, "HOLY BIBLE");
    snprintf(v->chap, sizeof v->chap, "Chapter");

    char dir[320], path[340];
    versionDir(v, dir, sizeof dir);
    snprintf(path, sizeof path, "%sinfo.txt", dir);
    FILE *f = fopen(path, "r");
    if (!f) return;
    readLine(f, v->name, sizeof v->name);
    readLine(f, v->cover, sizeof v->cover);
    readLine(f, v->chap, sizeof v->chap);
    fclose(f);
}

static void scanVersions(void) {
    nversions = 0;

    FILE *f = fopen(DATA_ROOT "books.txt", "r");
    if (f) {
        fclose(f);
        Version *v = &versions[nversions++];
        memset(v, 0, sizeof *v);
        readInfo(v);
    }

    DIR *d = opendir(DATA_ROOT);
    if (d) {
        struct dirent *e;
        while ((e = readdir(d)) != NULL && nversions < MAXVERS) {
            if (e->d_name[0] == '.' || strlen(e->d_name) >= sizeof versions[0].id) continue;
            char p[340];
            snprintf(p, sizeof p, DATA_ROOT "%s/books.txt", e->d_name);
            FILE *g = fopen(p, "r");
            if (!g) continue;
            fclose(g);
            Version *v = &versions[nversions];
            memset(v, 0, sizeof *v);
            snprintf(v->id, sizeof v->id, "%s", e->d_name);
            readInfo(v);
            nversions++;
        }
        closedir(d);
    }

    // sort by id
    for (int i = 0; i < nversions; i++)
        for (int j = i + 1; j < nversions; j++)
            if (strcmp(versions[i].id, versions[j].id) > 0) {
                Version tmp = versions[i]; versions[i] = versions[j]; versions[j] = tmp;
            }
}

static int findVersion(const char *id) {
    for (int i = 0; i < nversions; i++)
        if (strcmp(versions[i].id, id) == 0) return i;
    return -1;
}

static void loadBooks(void) {
    nbooks = 0;
    char path[340];
    snprintf(path, sizeof path, "%sbooks.txt", dataDir);
    FILE *f = fopen(path, "r");
    if (!f) return;
    char buf[256];
    while (nbooks < MAXBOOKS && fgets(buf, sizeof buf, f)) {
        Book *b = &books[nbooks];
        if (sscanf(buf, "%63[^|]|%47[^|]|%d", b->file, b->name, &b->chapters) == 3) nbooks++;
    }
    fclose(f);
}

static int linesOn(int pg) {
    float h = TEXT_BOT - TEXT_TOP - (pg == 0 ? HEADER_H : 0);
    int n = (int)(h / lh);
    return n < 1 ? 1 : n;
}

// Parses one word, measures it, and puts it on the current line/page.
static void placeWord(const char *w, float sc, u32 clr, float trail) {
    if (nitems >= MAXITEMS || curPage >= MAXPAGES - 1) return;
    Item *it = &items[nitems];
    if (!C2D_TextParse(&it->t, pageBuf, w)) return;
    C2D_TextOptimize(&it->t);
    float ww, hh;
    C2D_TextGetDimensions(&it->t, sc, sc, &ww, &hh);
    if (curX > 0 && curX + ww > TEXT_W) { curX = 0; curLine++; }
    if (curLine >= linesOn(curPage)) {
        curPage++; curLine = 0; curX = 0;
        pageStart[curPage] = nitems;
    }
    it->x = curX;
    it->y = TEXT_TOP + (curPage == 0 ? HEADER_H : 0) + curLine * lh;
    it->sc = sc;
    it->clr = clr;
    curX += ww + trail;
    nitems++;
}

static void layoutChapter(int book, int chapter) {
    C2D_TextBufClear(pageBuf);
    nitems = 0; curX = 0; curLine = 0; curPage = 0;
    pageStart[0] = 0;

    char path[400];
    snprintf(path, sizeof path, "%s%s", dataDir, books[book].file);
    FILE *f = fopen(path, "r");
    if (f) {
        static char buf[2048];
        while (fgets(buf, sizeof buf, f)) {
            buf[strcspn(buf, "\r\n")] = 0;
            char *p1 = strchr(buf, '|');
            if (!p1) continue;
            *p1 = 0;
            int ch = atoi(buf);
            if (ch < chapter) continue;
            if (ch > chapter) break;
            char *p2 = strchr(p1 + 1, '|');
            if (!p2) continue;
            *p2 = 0;
            placeWord(p1 + 1, NUM_SC, CLR_RED, 2.0f);   // verse number
            char *save = NULL;
            for (char *tok = strtok_r(p2 + 1, " ", &save); tok; tok = strtok_r(NULL, " ", &save))
                placeWord(tok, BODY_SC, CLR_INK, spaceW);
        }
        fclose(f);
    }
    pageCount = curPage + 1;
    pageStart[pageCount] = nitems;
}

static void savePos(void) {
    FILE *f = fopen(SAVE_FILE, "w");
    if (!f) return;
    const char *vid = (nversions > 0 && versions[curVer].id[0]) ? versions[curVer].id : "-";
    fprintf(f, "%d %d %d %s\n", curBook, curChapter, spread, vid);
    fclose(f);
}

static void openChapter(int book, int chapter, bool toEnd) {
    animOn = false;
    curBook = book; curChapter = chapter;
    layoutChapter(book, chapter);
    spread = toEnd ? ((pageCount - 1) & ~1) : 0;
}

// Switches to another translation. Keeps the same book
static void applyVersion(int idx) {
    curVer = idx;
    versionDir(&versions[idx], dataDir, sizeof dataDir);
    loadBooks();
    if (curBook >= nbooks) curBook = nbooks - 1;
    if (curBook >= 0) {
        if (curChapter > books[curBook].chapters) curChapter = books[curBook].chapters;
        if (curChapter < 1) curChapter = 1;
        openChapter(curBook, curChapter, false);
    }
    if (bookCur >= nbooks) bookCur = nbooks > 0 ? nbooks - 1 : 0;
}

static bool loadPos(void) {
    FILE *f = fopen(SAVE_FILE, "r");
    if (!f) return false;
    int b = -1, c = 0, s = 0;
    char vid[64] = "-";
    int n = fscanf(f, "%d %d %d %63s", &b, &c, &s, vid);
    fclose(f);

    int vi = findVersion(strcmp(vid, "-") == 0 ? "" : vid);
    if (vi < 0) vi = 0;
    applyVersion(vi);

    if (n < 2 || b < 0 || b >= nbooks || c < 1 || c > books[b].chapters) return false;
    openChapter(b, c, false);
    if (s < 0) s = 0;
    if (s >= pageCount) s = pageCount - 1;
    spread = s & ~1;
    return true;
}

static void nextSpread(void) {
    if (animOn) return;
    if (spread + 2 < pageCount) {
        animFrom = spread; spread += 2;
        animDir = 1; animFrame = 0; animOn = true;
    }
    else if (curChapter < books[curBook].chapters) openChapter(curBook, curChapter + 1, false);
    else if (curBook < nbooks - 1) openChapter(curBook + 1, 1, false);
    savePos();
}

static void prevSpread(void) {
    if (animOn) return;
    if (spread >= 2) {
        animFrom = spread; spread -= 2;
        animDir = -1; animFrame = 0; animOn = true;
    }
    else if (curChapter > 1) openChapter(curBook, curChapter - 1, true);
    else if (curBook > 0) openChapter(curBook - 1, books[curBook - 1].chapters, true);
    savePos();
}

static void nextChapter(void) {
    if (curChapter < books[curBook].chapters) openChapter(curBook, curChapter + 1, false);
    else if (curBook < nbooks - 1) openChapter(curBook + 1, 1, false);
    savePos();
}

static void prevChapter(void) {
    if (curChapter > 1) openChapter(curBook, curChapter - 1, false);
    else if (curBook > 0) openChapter(curBook - 1, books[curBook - 1].chapters, false);
    savePos();
}

static void setState(int s) { state = s; drag.active = false; animOn = false; }

static void goChapters(void) {
    chapCur = (bookCur == curBook) ? curChapter - 1 : 0;
    chapScroll = 0;
    ensureVisible(&chapScroll, (chapCur / GRID_COLS) * CELL_H, CELL_H, 240 - GRID_TOP);
    setState(ST_CHAPTERS);
}

static void goBooks(void) {
    bookCur = curBook >= 0 ? curBook : bookCur;
    ensureVisible(&bookScroll, bookCur * ROWH, ROWH, 240 - LIST_TOP);
    setState(ST_BOOKS);
}

static void goVersions(void) {
    verPrev = state;
    verCur = curVer;
    verScroll = 0;
    ensureVisible(&verScroll, verCur * ROWH, ROWH, 240 - LIST_TOP);
    setState(ST_VERSIONS);
}

static void leaveVersions(void) {
    if (verPrev == ST_READ && curBook >= 0) setState(ST_READ);
    else goBooks();
}

static void chooseVersion(int idx) {
    if (idx != curVer) {
        applyVersion(idx);
        if (curBook >= 0) savePos();
    }
    leaveVersions();
}

static void drawPage(float px, int pg, bool isTop) {
    R(px, 0, Z_PAGE, PAGE_W, 240, CLR_PARCH);
    RG(px, 0, Z_SHADE, 10, 240, SH_EDGE, SH_CLEAR, SH_EDGE, SH_CLEAR);
    RG(px + PAGE_W - 10, 0, Z_SHADE, 10, 240, SH_CLEAR, SH_EDGE, SH_CLEAR, SH_EDGE);
    if (isTop) RG(px, 204, Z_SHADE, PAGE_W, 36, SH_CLEAR, SH_CLEAR, SH_SPINE, SH_SPINE);
    else       RG(px, 0, Z_SHADE, PAGE_W, 36, SH_SPINE, SH_SPINE, SH_CLEAR, SH_CLEAR);


    drawText(isTop ? books[curBook].name : versions[curVer].name,
             px + PAGE_W / 2, 7, 0.42f, CLR_RED, 1, Z_TEXT);
    R(px + PAD_X, 26, Z_RULE, TEXT_W, 1, CLR_RULE);
    R(px + PAD_X, 208, Z_RULE, TEXT_W, 1, CLR_RULE);
    if (pg < pageCount) {
        char nb[16];
        snprintf(nb, sizeof nb, "%d", pg + 1);
        if (isTop) drawText(nb, px + PAGE_W / 2, 213, 0.45f, CLR_INK, 1, Z_TEXT);
        else       drawText(nb, px + PAGE_W - PAD_X, 7, 0.45f, CLR_INK, 2, Z_TEXT);
    }

    if (pg >= pageCount) return;

    // chapter heading on a chapter's first page
    if (pg == 0) {
        char ch[96];
        snprintf(ch, sizeof ch, "%s %d", versions[curVer].chap, curChapter);
        drawText(books[curBook].name, px + PAGE_W / 2, TEXT_TOP - 4,
                 fitScale(books[curBook].name, 0.85f, TEXT_W), CLR_INK, 1, Z_TEXT);
        drawText(ch, px + PAGE_W / 2, TEXT_TOP + 26, 0.5f, CLR_RED, 1, Z_TEXT);
        ornament(px + PAGE_W / 2, TEXT_TOP + 52, 70, CLR_GOLD, Z_RULE);
    }

    for (int i = pageStart[pg]; i < pageStart[pg + 1]; i++) {
        Item *it = &items[i];
        C2D_DrawText(&it->t, C2D_WithColor, TX(px + PAD_X + it->x), it->y, ZZ(Z_TEXT),
                     it->sc * xs, it->sc, it->clr);
    }
}

static void drawSpreadPage(float px, bool isTop, int off) {
    int newPg = spread + off;
    if (!animOn) { drawPage(px, newPg, isTop); return; }

    float t = (animFrame + 1) / (float)ANIM_FRAMES;
    if (t > 1.0f) t = 1.0f;
    float e = t * t * (3.0f - 2.0f * t);
    int oldPg = animFrom + off;
    float flipXs;

    if (animDir > 0) {
        drawPage(px, newPg, isTop);
        flipXs = 1.0f - e;
    } else {
        drawPage(px, oldPg, isTop);
        flipXs = e;
    }

    if (flipXs > 0.03f) {
        xp = px; xs = flipXs; zb = 0.52f; zm = 0.8f;
        drawPage(px, animDir > 0 ? oldPg : newPg, isTop);
        xs = 1.0f; xp = 0.0f; zb = 0.0f; zm = 1.0f;
    }

    // shadow cast
    float edge = px + PAGE_W * flipXs;
    if (edge < px + PAGE_W - 2) {
        float w = px + PAGE_W - edge;
        if (w > 26) w = 26;
        C2D_DrawRectangle(edge, 0, 0.55f, w, 240, SH_SPINE, SH_CLEAR, SH_SPINE, SH_CLEAR);
    }
}

static void drawControlBar(void) {
    static const char *labels[BTN_COUNT] = { "Books", "Chapters", "Version", "< Ch", "Ch >" };
    R(0, BTN_Y - 4, Z_BAR, 320, 31, CLR_PARCH);
    for (int i = 0; i < BTN_COUNT; i++) {
        float x = 8 + i * (BTN_W + BTN_GAP);
        R(x, BTN_Y, Z_BAR, BTN_W, BTN_H, CLR_PARCH_D);
        frameRect(x, BTN_Y, BTN_W, BTN_H, 1, CLR_RULE, Z_BAR);
        drawText(labels[i], x + BTN_W / 2, BTN_Y + 5, 0.4f, CLR_INK, 1, Z_BAR_TEXT);
    }
}

static void drawCover(const char *title, float titleSc, const char *sub) {
    frameRect(10, 10, 380, 220, 2, CLR_GOLD, Z_PAGE);
    frameRect(17, 17, 366, 206, 1, CLR_GOLD, Z_PAGE);
    drawText(title, 200, 62, fitScale(title, titleSc, 330), CLR_GOLD, 1, Z_TEXT);
    ornament(200, 128, 90, CLR_GOLD, Z_RULE);
    drawText(sub, 200, 142, fitScale(sub, 0.6f, 330), CLR_GOLD, 1, Z_TEXT);
}

static void drawHeaderBar(const char *title) {
    R(0, 0, Z_HDR, 320, LIST_TOP, CLR_LEATHER);
    R(0, LIST_TOP - 2, Z_HDR, 320, 2, CLR_GOLD);
    drawText(title, 160, 5, 0.6f, CLR_GOLD, 1, Z_HDR_TEXT);
}

static void drawBookList(void) {
    R(0, 0, Z_BG, 320, 240, CLR_PARCH);
    for (int i = 0; i < nbooks; i++) {
        float y = LIST_TOP + i * ROWH - bookScroll;
        if (y < LIST_TOP - ROWH || y > 240) continue;
        if (i == bookCur) {
            R(0, y, Z_PAGE, 320, ROWH, CLR_PARCH_D);
            R(0, y, Z_RULE, 4, ROWH, CLR_RED);
        }
        drawText(books[i].name, 16, y + 3, 0.55f, CLR_INK, 0, Z_TEXT);
        char tag[24];
        snprintf(tag, sizeof tag, "%s  %d", i < 39 ? "OT" : "NT", books[i].chapters);
        drawText(tag, 306, y + 6, 0.4f, CLR_RED, 2, Z_TEXT);
        R(12, y + ROWH - 1, Z_RULE, 296, 1, CLR_RULE);
    }
    drawHeaderBar("Select a Book");
    frameRect(244, 5, 70, 18, 1, CLR_GOLD, Z_HDR_TEXT);
    drawText("Version", 279, 7, 0.4f, CLR_GOLD, 1, Z_HDR_TEXT);
}

static void drawVersionList(void) {
    R(0, 0, Z_BG, 320, 240, CLR_PARCH);
    for (int i = 0; i < nversions; i++) {
        float y = LIST_TOP + i * ROWH - verScroll;
        if (y < LIST_TOP - ROWH || y > 240) continue;
        if (i == verCur) {
            R(0, y, Z_PAGE, 320, ROWH, CLR_PARCH_D);
            R(0, y, Z_RULE, 4, ROWH, CLR_RED);
        }
        drawText(versions[i].name, 16, y + 3, fitScale(versions[i].name, 0.55f, 210), CLR_INK, 0, Z_TEXT);
        const char *tag = (i == curVer) ? "current" : (versions[i].id[0] ? versions[i].id : "default");
        drawText(tag, 306, y + 6, 0.4f, CLR_RED, 2, Z_TEXT);
        R(12, y + ROWH - 1, Z_RULE, 296, 1, CLR_RULE);
    }
    drawHeaderBar("Select a Version");
}

static void drawChapterGrid(void) {
    int n = books[bookCur].chapters;
    R(0, 0, Z_BG, 320, 240, CLR_PARCH);
    for (int i = 0; i < n; i++) {
        float x = GRID_X + (i % GRID_COLS) * CELL_W;
        float y = GRID_TOP + (i / GRID_COLS) * CELL_H - chapScroll;
        if (y < GRID_TOP - CELL_H || y > 240) continue;
        bool sel = (i == chapCur);
        R(x + 2, y + 2, Z_PAGE, CELL_W - 4, CELL_H - 4, sel ? CLR_RED : CLR_PARCH_D);
        char s[16];
        snprintf(s, sizeof s, "%d", i + 1);
        drawText(s, x + CELL_W / 2, y + 10, 0.6f, sel ? CLR_PARCH : CLR_INK, 1, Z_TEXT);
    }
    char h[160];
    snprintf(h, sizeof h, "%s - %s", books[bookCur].name, versions[curVer].chap);
    drawHeaderBar(h);
}

int main(void) {
    gfxInitDefault();
    C3D_Init(C3D_DEFAULT_CMDBUF_SIZE);
    C2D_Init(C2D_DEFAULT_MAX_OBJECTS);
    C2D_Prepare();
    topT = C2D_CreateScreenTarget(GFX_TOP, GFX_LEFT);
    botT = C2D_CreateScreenTarget(GFX_BOTTOM, GFX_LEFT);
    dynBuf = C2D_TextBufNew(4096);
    pageBuf = C2D_TextBufNew(GLYPHS);

    // measure line height and space width once
    {
        C2D_Text t;
        float w1, w2, h;
        C2D_TextParse(&t, dynBuf, "Ag");
        C2D_TextGetDimensions(&t, BODY_SC, BODY_SC, &w1, &h);
        lh = h + 3.0f;
        C2D_TextParse(&t, dynBuf, "n n");
        C2D_TextGetDimensions(&t, BODY_SC, BODY_SC, &w1, &h);
        C2D_TextParse(&t, dynBuf, "nn");
        C2D_TextGetDimensions(&t, BODY_SC, BODY_SC, &w2, &h);
        spaceW = w1 - w2;
        if (spaceW < 2.0f) spaceW = 4.0f;
    }

    scanVersions();
    if (nversions > 0) {
        if (loadPos()) { bookCur = curBook; state = ST_READ; }
        else if (nbooks == 0) applyVersion(0);
    }

    while (aptMainLoop()) {
        hidScanInput();
        u32 kDown = hidKeysDown(), kHeld = hidKeysHeld(), kUp = hidKeysUp();
        touchPosition tp;
        hidTouchRead(&tp);
        if (kDown & KEY_START) break;

        if (animOn) {
            animFrame++;
            if (animFrame >= ANIM_FRAMES) animOn = false;
        }

        // update
        if (nversions > 0) {
            if (state == ST_VERSIONS) {
                u32 nav = navKeys(kDown, kHeld);
                if ((nav & KEY_DDOWN) && verCur < nversions - 1) verCur++;
                if ((nav & KEY_DUP) && verCur > 0) verCur--;
                if (nav) ensureVisible(&verScroll, verCur * ROWH, ROWH, 240 - LIST_TOP);

                int tx, ty;
                bool pick = false;
                if (dragUpdate(kDown, kHeld, kUp, tp, &verScroll, &tx, &ty) && ty >= LIST_TOP) {
                    int r = (int)((ty - LIST_TOP + verScroll) / ROWH);
                    if (r >= 0 && r < nversions) { verCur = r; pick = true; }
                }
                verScroll = clampf(verScroll, 0, clampf(nversions * ROWH - (240 - LIST_TOP), 0, 100000));
                if (kDown & KEY_A) pick = true;
                if (pick) chooseVersion(verCur);
                else if ((kDown & KEY_B) && nbooks > 0) leaveVersions();

            } else if (nbooks == 0) {
                if (kDown & KEY_Y) goVersions();

            } else if (state == ST_BOOKS) {
                u32 nav = navKeys(kDown, kHeld);
                if ((nav & KEY_DDOWN) && bookCur < nbooks - 1) bookCur++;
                if ((nav & KEY_DUP) && bookCur > 0) bookCur--;
                if (nav & KEY_DRIGHT) bookCur = (bookCur + 8 < nbooks) ? bookCur + 8 : nbooks - 1;
                if (nav & KEY_DLEFT) bookCur = (bookCur - 8 > 0) ? bookCur - 8 : 0;
                if (nav) ensureVisible(&bookScroll, bookCur * ROWH, ROWH, 240 - LIST_TOP);

                int tx, ty;
                if (dragUpdate(kDown, kHeld, kUp, tp, &bookScroll, &tx, &ty)) {
                    if (ty >= LIST_TOP) {
                        int r = (int)((ty - LIST_TOP + bookScroll) / ROWH);
                        if (r >= 0 && r < nbooks) { bookCur = r; goChapters(); }
                    } else if (tx >= 240) {
                        goVersions();
                    }
                }
                bookScroll = clampf(bookScroll, 0, clampf(nbooks * ROWH - (240 - LIST_TOP), 0, 100000));
                if (kDown & KEY_A) goChapters();
                else if (kDown & KEY_Y) goVersions();
                else if ((kDown & KEY_B) && curBook >= 0) setState(ST_READ);

            } else if (state == ST_CHAPTERS) {
                int n = books[bookCur].chapters;
                u32 nav = navKeys(kDown, kHeld);
                if ((nav & KEY_DRIGHT) && chapCur < n - 1) chapCur++;
                if ((nav & KEY_DLEFT) && chapCur > 0) chapCur--;
                if ((nav & KEY_DDOWN)) chapCur = (chapCur + GRID_COLS < n) ? chapCur + GRID_COLS : n - 1;
                if ((nav & KEY_DUP)) chapCur = (chapCur - GRID_COLS >= 0) ? chapCur - GRID_COLS : 0;
                if (nav) ensureVisible(&chapScroll, (chapCur / GRID_COLS) * CELL_H, CELL_H, 240 - GRID_TOP);

                int tx, ty;
                bool open = false;
                if (dragUpdate(kDown, kHeld, kUp, tp, &chapScroll, &tx, &ty) && ty >= GRID_TOP) {
                    int col = (tx - GRID_X) / CELL_W;
                    int row = (int)((ty - GRID_TOP + chapScroll) / CELL_H);
                    int idx = row * GRID_COLS + col;
                    if (tx >= GRID_X && col < GRID_COLS && idx >= 0 && idx < n) { chapCur = idx; open = true; }
                }
                int rows = (n + GRID_COLS - 1) / GRID_COLS;
                chapScroll = clampf(chapScroll, 0, clampf(rows * CELL_H - (240 - GRID_TOP) + 4, 0, 100000));
                if (kDown & KEY_A) open = true;
                if (open) {
                    openChapter(bookCur, chapCur + 1, false);
                    savePos();
                    setState(ST_READ);
                }
                if (kDown & KEY_B) goBooks();

            } else {
                if (kDown & (KEY_DRIGHT | KEY_A)) nextSpread();
                if (kDown & KEY_DLEFT) prevSpread();
                if (kDown & KEY_R) nextChapter();
                if (kDown & KEY_L) prevChapter();
                if (kDown & KEY_X) { bookCur = curBook; goChapters(); }
                else if (kDown & KEY_Y) goVersions();
                else if (kDown & KEY_B) goBooks();
                else if (kDown & KEY_TOUCH) {
                    if (tp.py >= BTN_Y - 4) {
                        for (int i = 0; i < BTN_COUNT; i++) {
                            int bx = 8 + i * (BTN_W + BTN_GAP);
                            if (tp.px >= bx && tp.px < bx + BTN_W) {
                                if (i == 0) goBooks();
                                else if (i == 1) { bookCur = curBook; goChapters(); }
                                else if (i == 2) goVersions();
                                else if (i == 3) prevChapter();
                                else nextChapter();
                                break;
                            }
                        }
                    } else if (tp.px < 110) prevSpread();
                    else if (tp.px > 210) nextSpread();
                }
            }
        }

        // draw
        C2D_TextBufClear(dynBuf);
        C3D_FrameBegin(C3D_FRAME_SYNCDRAW);

        C2D_TargetClear(topT, CLR_LEATHER);
        C2D_SceneBegin(topT);
        if (nversions == 0) {
            drawText("Could not find any Bible data", 200, 90, 0.7f, CLR_GOLD, 1, Z_TEXT);
            drawText("Expected in sdmc:/3ds/3DSBible/data/", 200, 120, 0.5f, CLR_GOLD, 1, Z_TEXT);
        } else if (state == ST_VERSIONS) {
            drawCover(versions[verCur].cover, 1.2f, versions[verCur].name);
        } else if (nbooks == 0) {
            drawText("This version has no books", 200, 100, 0.7f, CLR_GOLD, 1, Z_TEXT);
            drawText("Press Y to choose another", 200, 130, 0.5f, CLR_GOLD, 1, Z_TEXT);
        } else if (state == ST_READ) {
            R(34, 0, Z_BG + 0.05f, 6, 240, CLR_PARCH_D);
            R(30, 0, Z_BG + 0.05f, 2, 240, CLR_RULE);
            R(360, 0, Z_BG + 0.05f, 6, 240, CLR_PARCH_D);
            R(368, 0, Z_BG + 0.05f, 2, 240, CLR_RULE);
            drawSpreadPage(40, true, 0);
        } else if (state == ST_CHAPTERS) {
            drawCover(books[bookCur].name, 0.95f, "Choose a chapter");
        } else {
            drawCover(versions[curVer].cover, 1.2f, versions[curVer].name);
        }

        C2D_TargetClear(botT, CLR_LEATHER);
        C2D_SceneBegin(botT);
        if (nversions == 0) {
            drawText("Press START to exit", 160, 110, 0.6f, CLR_GOLD, 1, Z_TEXT);
        } else if (state == ST_VERSIONS) {
            drawVersionList();
        } else if (nbooks == 0) {
            drawText("Press START to exit", 160, 110, 0.6f, CLR_GOLD, 1, Z_TEXT);
        } else if (state == ST_READ) {
            drawSpreadPage(0, false, 1);
            drawControlBar();
            bool hasPrev = !(curBook == 0 && curChapter == 1 && spread == 0);
            bool hasNext = !(curBook == nbooks - 1 && curChapter == books[curBook].chapters && spread + 2 >= pageCount);
            if (hasPrev) TRI(5, 120, 15, 111, 15, 129, CLR_ARROW, Z_BAR);
            if (hasNext) TRI(315, 120, 305, 111, 305, 129, CLR_ARROW, Z_BAR);
        } else if (state == ST_CHAPTERS) {
            drawChapterGrid();
        } else {
            drawBookList();
        }

        C3D_FrameEnd(0);
    }

    C2D_TextBufDelete(pageBuf);
    C2D_TextBufDelete(dynBuf);
    C2D_Fini();
    C3D_Fini();
    gfxExit();
    return 0;
}
