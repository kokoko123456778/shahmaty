// =====================================================================
//  ШАХМАТЫ — игра в один файл для Android и ПК.
//  Только SDL2. Всё рисуется кодом: доска, фигуры, кнопки, шрифт.
//
//  Сборка на ПК:  g++ -std=c++17 -O2 shahmaty.cpp -o shahmaty $(sdl2-config --cflags --libs)
//  Проверка правил: ./shahmaty --perft 4      (20, 400, 8902, 197281)
//                   ./shahmaty --selftest
// =====================================================================
#include <SDL2/SDL.h>

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#if defined(__unix__) || defined(__ANDROID__) || defined(__APPLE__)
#include <unistd.h>
#define SHAH_HAVE_FSYNC 1
#endif

// Сеть: системные сокеты ОС (не отдельная библиотека). На Android нужно
// разрешение android.permission.INTERNET в манифесте приложения.
#if defined(_WIN32)
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <winsock2.h>
#include <ws2tcpip.h>
#ifdef _MSC_VER
#pragma comment(lib, "ws2_32.lib")
#endif
typedef SOCKET sock_t;
#define SOCK_BAD INVALID_SOCKET
static bool sockWouldBlock() {
    int e = WSAGetLastError();
    return e == WSAEWOULDBLOCK || e == WSAEINPROGRESS || e == WSAEALREADY;
}
static void sockClose(sock_t s) { closesocket(s); }
static void sockNonBlock(sock_t s) {
    u_long m = 1;
    ioctlsocket(s, FIONBIO, &m);
}
#else
#include <arpa/inet.h>
#include <cerrno>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>
typedef int sock_t;
#define SOCK_BAD (-1)
static bool sockWouldBlock() { return errno == EWOULDBLOCK || errno == EAGAIN || errno == EINPROGRESS || errno == EINTR; }
static void sockClose(sock_t s) { close(s); }
static void sockNonBlock(sock_t s) {
    int f = fcntl(s, F_GETFL, 0);
    fcntl(s, F_SETFL, f | O_NONBLOCK);
}
#endif
#ifndef MSG_NOSIGNAL
#define MSG_NOSIGNAL 0
#endif

// =====================================================================
//                             ДВИЖОК
// =====================================================================
namespace eng {

enum { EMPTY = 0, PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6 };
enum { WHITE = 0, BLACK = 1 };
enum { F_CAP = 1, F_EP = 2, F_CASTLE = 4, F_DOUBLE = 8 };

typedef uint32_t Move;
static inline Move mkMove(int f, int t, int promo = 0, int fl = 0) {
    return (Move)(f | (t << 6) | (promo << 12) | (fl << 15));
}
static inline int mFrom(Move m) { return (int)(m & 63); }
static inline int mTo(Move m) { return (int)((m >> 6) & 63); }
static inline int mPromo(Move m) { return (int)((m >> 12) & 7); }
static inline int mFlags(Move m) { return (int)((m >> 15) & 15); }
static inline int pType(int p) { return p & 7; }
static inline int pColor(int p) { return p >> 3; }
static inline int mkPiece(int c, int t) { return c * 8 + t; }

static uint64_t zP[16][64], zSide, zCastle[16], zEp[8];
static int8_t rays[64][8][8], rayLen[64][8];
static int8_t knT[64][8], knN[64], kgT[64][8], kgN[64];
static int castleMask[64];
static bool g_inited = false;

static uint64_t splitmix(uint64_t &s) {
    uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static const int DIR_F[8] = {1, -1, 0, 0, 1, 1, -1, -1};
static const int DIR_R[8] = {0, 0, 1, -1, 1, -1, 1, -1};
static const int KN_F[8] = {1, 2, 2, 1, -1, -2, -2, -1};
static const int KN_R[8] = {2, 1, -1, -2, -2, -1, 1, 2};

static void init() {
    if (g_inited) return;
    g_inited = true;
    uint64_t s = 0x5EED1234ABCDULL;
    for (int p = 0; p < 16; p++)
        for (int q = 0; q < 64; q++) zP[p][q] = splitmix(s);
    zSide = splitmix(s);
    for (int i = 0; i < 16; i++) zCastle[i] = splitmix(s);
    for (int i = 0; i < 8; i++) zEp[i] = splitmix(s);
    for (int q = 0; q < 64; q++) {
        int f = q & 7, r = q >> 3;
        for (int d = 0; d < 8; d++) {
            int n = 0, ff = f + DIR_F[d], rr = r + DIR_R[d];
            while (ff >= 0 && ff < 8 && rr >= 0 && rr < 8) {
                rays[q][d][n++] = (int8_t)(rr * 8 + ff);
                ff += DIR_F[d];
                rr += DIR_R[d];
            }
            rayLen[q][d] = (int8_t)n;
        }
        int kn = 0;
        for (int i = 0; i < 8; i++) {
            int ff = f + KN_F[i], rr = r + KN_R[i];
            if (ff >= 0 && ff < 8 && rr >= 0 && rr < 8) knT[q][kn++] = (int8_t)(rr * 8 + ff);
        }
        knN[q] = (int8_t)kn;
        int kg = 0;
        for (int df = -1; df <= 1; df++)
            for (int dr = -1; dr <= 1; dr++) {
                if (!df && !dr) continue;
                int ff = f + df, rr = r + dr;
                if (ff >= 0 && ff < 8 && rr >= 0 && rr < 8) kgT[q][kg++] = (int8_t)(rr * 8 + ff);
            }
        kgN[q] = (int8_t)kg;
        castleMask[q] = 15;
    }
    castleMask[0] = 15 & ~2;
    castleMask[7] = 15 & ~1;
    castleMask[4] = 15 & ~3;
    castleMask[56] = 15 & ~8;
    castleMask[63] = 15 & ~4;
    castleMask[60] = 15 & ~12;
}

struct MoveList {
    Move m[512];  // с запасом: в своей расстановке может быть много ферзей
    int n = 0;
    void add(Move x) {
        if (n < 512) m[n++] = x;
    }
};

struct Undo {
    Move m;
    int captured, castle, ep, half;
    uint64_t hash;
};

struct Board {
    int sq[64];
    int side = WHITE, castle = 0, ep = -1, half = 0, full = 1;
    int kingSq[2] = {4, 60};
    uint64_t hash = 0;

    uint64_t computeHash() const {
        uint64_t h = 0;
        for (int i = 0; i < 64; i++)
            if (sq[i]) h ^= zP[sq[i]][i];
        if (side) h ^= zSide;
        h ^= zCastle[castle];
        if (ep >= 0) h ^= zEp[ep & 7];
        return h;
    }

    // Поле взятия на проходе ставим, только если взятие возможно (важно для повторений)
    bool epUseful(int epSq, int sideToMove) const {
        int pawnRank = sideToMove == WHITE ? 4 : 3;
        int f = epSq & 7;
        int P = mkPiece(sideToMove, PAWN);
        if (f > 0 && sq[pawnRank * 8 + f - 1] == P) return true;
        if (f < 7 && sq[pawnRank * 8 + f + 1] == P) return true;
        return false;
    }

    bool setFEN(const std::string &fen) {
        for (int i = 0; i < 64; i++) sq[i] = 0;
        size_t i = 0;
        int r = 7, f = 0;
        kingSq[0] = kingSq[1] = -1;
        while (i < fen.size() && fen[i] != ' ') {
            char ch = fen[i++];
            if (ch == '/') { r--; f = 0; continue; }
            if (ch >= '1' && ch <= '8') { f += ch - '0'; continue; }
            int c = (ch >= 'a' && ch <= 'z') ? BLACK : WHITE;
            int t = 0;
            switch (ch | 32) {
                case 'p': t = PAWN; break;
                case 'n': t = KNIGHT; break;
                case 'b': t = BISHOP; break;
                case 'r': t = ROOK; break;
                case 'q': t = QUEEN; break;
                case 'k': t = KING; break;
                default: return false;
            }
            if (r < 0 || f > 7) return false;
            sq[r * 8 + f] = mkPiece(c, t);
            if (t == KING) kingSq[c] = r * 8 + f;
            f++;
        }
        if (kingSq[0] < 0 || kingSq[1] < 0) return false;
        while (i < fen.size() && fen[i] == ' ') i++;
        side = (i < fen.size() && fen[i] == 'b') ? BLACK : WHITE;
        i++;
        while (i < fen.size() && fen[i] == ' ') i++;
        castle = 0;
        while (i < fen.size() && fen[i] != ' ') {
            char ch = fen[i++];
            if (ch == 'K') castle |= 1;
            if (ch == 'Q') castle |= 2;
            if (ch == 'k') castle |= 4;
            if (ch == 'q') castle |= 8;
        }
        while (i < fen.size() && fen[i] == ' ') i++;
        ep = -1;
        if (i + 1 < fen.size() && fen[i] >= 'a' && fen[i] <= 'h') {
            int e = (fen[i + 1] - '1') * 8 + (fen[i] - 'a');
            if (e >= 0 && e < 64 && epUseful(e, side)) ep = e;
            i += 2;
        } else if (i < fen.size()) {
            i++;
        }
        half = 0;
        full = 1;
        if (i < fen.size()) {
            int h = 0, fm = 1;
            if (sscanf(fen.c_str() + i, "%d %d", &h, &fm) >= 1) {
                half = h;
                full = fm;
            }
        }
        hash = computeHash();
        return true;
    }

    void setStart() { setFEN("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"); }

    bool attacked(int s, int by) const {
        int f = s & 7;
        if (by == WHITE) {
            int P = mkPiece(WHITE, PAWN);
            if (s >= 8) {
                if (f > 0 && sq[s - 9] == P) return true;
                if (f < 7 && sq[s - 7] == P) return true;
            }
        } else {
            int P = mkPiece(BLACK, PAWN);
            if (s < 56) {
                if (f < 7 && sq[s + 9] == P) return true;
                if (f > 0 && sq[s + 7] == P) return true;
            }
        }
        int N = mkPiece(by, KNIGHT);
        for (int i = 0; i < knN[s]; i++)
            if (sq[knT[s][i]] == N) return true;
        int K = mkPiece(by, KING);
        for (int i = 0; i < kgN[s]; i++)
            if (sq[kgT[s][i]] == K) return true;
        int Rk = mkPiece(by, ROOK), Bs = mkPiece(by, BISHOP), Q = mkPiece(by, QUEEN);
        for (int d = 0; d < 8; d++) {
            for (int i = 0; i < rayLen[s][d]; i++) {
                int p = sq[rays[s][d][i]];
                if (!p) continue;
                if (p == Q || (d < 4 ? p == Rk : p == Bs)) return true;
                break;
            }
        }
        return false;
    }

    bool inCheck(int c) const { return attacked(kingSq[c], c ^ 1); }

    void addPawn(MoveList &ml, int f, int t, int fl, bool promo, bool capsOnly) const {
        if (promo) {
            ml.add(mkMove(f, t, QUEEN, fl));
            if (!capsOnly) {
                ml.add(mkMove(f, t, KNIGHT, fl));
                ml.add(mkMove(f, t, ROOK, fl));
                ml.add(mkMove(f, t, BISHOP, fl));
            }
        } else {
            ml.add(mkMove(f, t, 0, fl));
        }
    }

    void genCastles(MoveList &ml, int s) const {
        int c = side, them = c ^ 1;
        int Rk = mkPiece(c, ROOK);
        if (c == WHITE) {
            if (s != 4) return;
            if ((castle & 1) && !sq[5] && !sq[6] && sq[7] == Rk && !attacked(4, them) && !attacked(5, them) &&
                !attacked(6, them))
                ml.add(mkMove(4, 6, 0, F_CASTLE));
            if ((castle & 2) && !sq[3] && !sq[2] && !sq[1] && sq[0] == Rk && !attacked(4, them) &&
                !attacked(3, them) && !attacked(2, them))
                ml.add(mkMove(4, 2, 0, F_CASTLE));
        } else {
            if (s != 60) return;
            if ((castle & 4) && !sq[61] && !sq[62] && sq[63] == Rk && !attacked(60, them) && !attacked(61, them) &&
                !attacked(62, them))
                ml.add(mkMove(60, 62, 0, F_CASTLE));
            if ((castle & 8) && !sq[59] && !sq[58] && !sq[57] && sq[56] == Rk && !attacked(60, them) &&
                !attacked(59, them) && !attacked(58, them))
                ml.add(mkMove(60, 58, 0, F_CASTLE));
        }
    }

    // Псевдолегальные ходы
    void gen(MoveList &ml, bool capsOnly) const {
        ml.n = 0;
        int c = side, them = c ^ 1;
        for (int s = 0; s < 64; s++) {
            int p = sq[s];
            if (!p || pColor(p) != c) continue;
            int t = pType(p);
            if (t == PAWN) {
                int dir = c == WHITE ? 8 : -8;
                int r = s >> 3, f = s & 7;
                bool promo = (c == WHITE ? r == 6 : r == 1);
                int to = s + dir;
                if (!sq[to]) {
                    if (promo)
                        addPawn(ml, s, to, 0, true, capsOnly);
                    else if (!capsOnly) {
                        ml.add(mkMove(s, to));
                        bool start = (c == WHITE ? r == 1 : r == 6);
                        if (start && !sq[to + dir]) ml.add(mkMove(s, to + dir, 0, F_DOUBLE));
                    }
                }
                for (int df = -1; df <= 1; df += 2) {
                    int ff = f + df;
                    if (ff < 0 || ff > 7) continue;
                    int tt = to + df;
                    int q = sq[tt];
                    if (q && pColor(q) == them)
                        addPawn(ml, s, tt, F_CAP, promo, capsOnly);
                    else if (tt == ep)
                        ml.add(mkMove(s, tt, 0, F_CAP | F_EP));
                }
            } else if (t == KNIGHT || t == KING) {
                const int8_t *T = t == KNIGHT ? knT[s] : kgT[s];
                int n = t == KNIGHT ? knN[s] : kgN[s];
                for (int i = 0; i < n; i++) {
                    int tt = T[i];
                    int q = sq[tt];
                    if (!q) {
                        if (!capsOnly) ml.add(mkMove(s, tt));
                    } else if (pColor(q) == them) {
                        ml.add(mkMove(s, tt, 0, F_CAP));
                    }
                }
                if (t == KING && !capsOnly) genCastles(ml, s);
            } else {
                int d0 = t == BISHOP ? 4 : 0, d1 = t == ROOK ? 4 : 8;
                for (int d = d0; d < d1; d++) {
                    for (int i = 0; i < rayLen[s][d]; i++) {
                        int tt = rays[s][d][i];
                        int q = sq[tt];
                        if (!q) {
                            if (!capsOnly) ml.add(mkMove(s, tt));
                            continue;
                        }
                        if (pColor(q) == them) ml.add(mkMove(s, tt, 0, F_CAP));
                        break;
                    }
                }
            }
        }
    }

    void make(Move m, Undo &u) {
        u.m = m;
        u.castle = castle;
        u.ep = ep;
        u.half = half;
        u.hash = hash;
        int f = mFrom(m), t = mTo(m), fl = mFlags(m);
        int p = sq[f];
        int c = side;
        int cap = sq[t];
        if (fl & F_EP) {
            int cs = t + (c == WHITE ? -8 : 8);
            cap = sq[cs];
            sq[cs] = 0;
            hash ^= zP[cap][cs];
        } else if (cap) {
            hash ^= zP[cap][t];
        }
        u.captured = cap;
        hash ^= zP[p][f];
        sq[f] = 0;
        int np = mPromo(m) ? mkPiece(c, mPromo(m)) : p;
        sq[t] = np;
        hash ^= zP[np][t];
        if (pType(p) == KING) {
            kingSq[c] = t;
            if (fl & F_CASTLE) {
                int rf, rt;
                if (t > f) { rf = t + 1; rt = t - 1; }
                else { rf = t - 2; rt = t + 1; }
                int rk = sq[rf];
                sq[rf] = 0;
                sq[rt] = rk;
                hash ^= zP[rk][rf] ^ zP[rk][rt];
            }
        }
        if (ep >= 0) hash ^= zEp[ep & 7];
        ep = -1;
        if (fl & F_DOUBLE) {
            int e = (f + t) / 2;
            if (epUseful(e, c ^ 1)) {
                ep = e;
                hash ^= zEp[ep & 7];
            }
        }
        hash ^= zCastle[castle];
        castle &= castleMask[f] & castleMask[t];
        hash ^= zCastle[castle];
        half = (pType(p) == PAWN || cap) ? 0 : half + 1;
        if (c == BLACK) full++;
        side ^= 1;
        hash ^= zSide;
    }

    void unmake(const Undo &u) {
        side ^= 1;
        int c = side;
        Move m = u.m;
        int f = mFrom(m), t = mTo(m), fl = mFlags(m);
        int np = sq[t];
        int p = mPromo(m) ? mkPiece(c, PAWN) : np;
        sq[f] = p;
        if (fl & F_EP) {
            sq[t] = 0;
            sq[t + (c == WHITE ? -8 : 8)] = u.captured;
        } else {
            sq[t] = u.captured;
        }
        if (pType(p) == KING) {
            kingSq[c] = f;
            if (fl & F_CASTLE) {
                int rf, rt;
                if (t > f) { rf = t + 1; rt = t - 1; }
                else { rf = t - 2; rt = t + 1; }
                sq[rf] = sq[rt];
                sq[rt] = 0;
            }
        }
        castle = u.castle;
        ep = u.ep;
        half = u.half;
        hash = u.hash;
        if (c == BLACK) full--;
    }

    void makeNull(Undo &u) {
        u.m = 0;
        u.castle = castle;
        u.ep = ep;
        u.half = half;
        u.hash = hash;
        u.captured = 0;
        if (ep >= 0) hash ^= zEp[ep & 7];
        ep = -1;
        half++;
        side ^= 1;
        hash ^= zSide;
    }
    void unmakeNull(const Undo &u) {
        side ^= 1;
        ep = u.ep;
        half = u.half;
        hash = u.hash;
    }

    void genLegal(MoveList &out) {
        MoveList ml;
        gen(ml, false);
        out.n = 0;
        for (int i = 0; i < ml.n; i++) {
            Undo u;
            make(ml.m[i], u);
            if (!attacked(kingSq[side ^ 1], side)) out.add(ml.m[i]);
            unmake(u);
        }
    }

    // Ничья по недостатку материала: K-K, K+лёгкая фигура против K, только слоны одного цвета полей
    bool insufficient() const {
        int knights = 0, bl = 0, bd = 0;
        for (int s = 0; s < 64; s++) {
            int p = sq[s];
            if (!p) continue;
            int t = pType(p);
            if (t == PAWN || t == ROOK || t == QUEEN) return false;
            if (t == KNIGHT) knights++;
            if (t == BISHOP) {
                if (((s & 7) + (s >> 3)) & 1) bl++;
                else bd++;
            }
        }
        if (knights + bl + bd <= 1) return true;
        if (knights == 0 && (bl == 0 || bd == 0)) return true;
        return false;
    }

    // Может ли цвет c хоть как-то поставить мат (для проигрыша по времени)
    bool canMate(int c) const {
        int minors = 0, other = 0;
        for (int s = 0; s < 64; s++) {
            int p = sq[s];
            if (!p) continue;
            int t = pType(p);
            if (pColor(p) == c) {
                if (t == PAWN || t == ROOK || t == QUEEN) return true;
                if (t == KNIGHT || t == BISHOP) minors++;
            } else if (t != KING) {
                other++;
            }
        }
        if (minors >= 2) return true;
        if (minors == 1 && other > 0) return true;
        return false;
    }

    bool hasNonPawn(int c) const {
        for (int s = 0; s < 64; s++) {
            int p = sq[s];
            if (p && pColor(p) == c && pType(p) != PAWN && pType(p) != KING) return true;
        }
        return false;
    }
};

static uint64_t perft(Board &b, int d) {
    MoveList ml;
    b.gen(ml, false);
    uint64_t n = 0;
    for (int i = 0; i < ml.n; i++) {
        Undo u;
        b.make(ml.m[i], u);
        if (!b.attacked(b.kingSq[b.side ^ 1], b.side)) n += d <= 1 ? 1 : perft(b, d - 1);
        b.unmake(u);
    }
    return n;
}

// ---------- запись ходов ----------
static const char *PIECE_RU[7] = {"", "", "К", "С", "Л", "Ф", "Кр"};

static std::string sqName(int s) {
    std::string r;
    r += (char)('a' + (s & 7));
    r += (char)('1' + (s >> 3));
    return r;
}

static std::string toSAN(const Board &b0, Move m) {
    Board b = b0;
    std::string s;
    int f = mFrom(m), t = mTo(m), fl = mFlags(m);
    int p = pType(b.sq[f]);
    if (fl & F_CASTLE) {
        s = (t > f) ? "0-0" : "0-0-0";
    } else if (p == PAWN) {
        if (fl & F_CAP) {
            s += (char)('a' + (f & 7));
            s += "x";
        }
        s += sqName(t);
        if (mPromo(m)) s += PIECE_RU[mPromo(m)];
    } else {
        s += PIECE_RU[p];
        MoveList ml;
        b.genLegal(ml);
        bool amb = false, sameF = false, sameR = false;
        for (int i = 0; i < ml.n; i++) {
            Move o = ml.m[i];
            if (mTo(o) != t || mFrom(o) == f) continue;
            if (pType(b.sq[mFrom(o)]) != p) continue;
            amb = true;
            if ((mFrom(o) & 7) == (f & 7)) sameF = true;
            if ((mFrom(o) >> 3) == (f >> 3)) sameR = true;
        }
        if (amb) {
            if (!sameF) s += (char)('a' + (f & 7));
            else if (!sameR) s += (char)('1' + (f >> 3));
            else s += sqName(f);
        }
        if (fl & F_CAP) s += "x";
        s += sqName(t);
    }
    Undo u;
    b.make(m, u);
    if (b.inCheck(b.side)) {
        MoveList ml;
        b.genLegal(ml);
        s += ml.n ? "+" : "#";
    }
    return s;
}

static std::string toUCI(Move m) {
    std::string s = sqName(mFrom(m)) + sqName(mTo(m));
    static const char PR[8] = {' ', ' ', 'n', 'b', 'r', 'q', ' ', ' '};
    if (mPromo(m)) s += PR[mPromo(m)];
    return s;
}

// ---------- оценка позиции ----------
static const int VAL[7] = {0, 100, 320, 330, 500, 900, 0};

// Таблицы с точки зрения белых, первая строка — 8-я горизонталь
static const int PST_P[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0};
static const int PST_N[64] = {
   -50,-40,-30,-30,-30,-30,-40,-50,
   -40,-20,  0,  0,  0,  0,-20,-40,
   -30,  0, 10, 15, 15, 10,  0,-30,
   -30,  5, 15, 20, 20, 15,  5,-30,
   -30,  0, 15, 20, 20, 15,  0,-30,
   -30,  5, 10, 15, 15, 10,  5,-30,
   -40,-20,  0,  5,  5,  0,-20,-40,
   -50,-40,-30,-30,-30,-30,-40,-50};
static const int PST_B[64] = {
   -20,-10,-10,-10,-10,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5, 10, 10,  5,  0,-10,
   -10,  5,  5, 10, 10,  5,  5,-10,
   -10,  0, 10, 10, 10, 10,  0,-10,
   -10, 10, 10, 10, 10, 10, 10,-10,
   -10,  5,  0,  0,  0,  0,  5,-10,
   -20,-10,-10,-10,-10,-10,-10,-20};
static const int PST_R[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0};
static const int PST_Q[64] = {
   -20,-10,-10, -5, -5,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5,  5,  5,  5,  0,-10,
    -5,  0,  5,  5,  5,  5,  0, -5,
     0,  0,  5,  5,  5,  5,  0, -5,
   -10,  5,  5,  5,  5,  5,  0,-10,
   -10,  0,  5,  0,  0,  0,  0,-10,
   -20,-10,-10, -5, -5,-10,-10,-20};
static const int PST_KMG[64] = {
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -20,-30,-30,-40,-40,-30,-30,-20,
   -10,-20,-20,-20,-20,-20,-20,-10,
    20, 20,  0,  0,  0,  0, 20, 20,
    20, 30, 10,  0,  0, 10, 30, 20};
static const int PST_KEG[64] = {
   -50,-40,-30,-20,-20,-30,-40,-50,
   -30,-20,-10,  0,  0,-10,-20,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-30,  0,  0,  0,  0,-30,-30,
   -50,-30,-30,-30,-30,-30,-30,-50};
static const int *PST[7] = {nullptr, PST_P, PST_N, PST_B, PST_R, PST_Q, PST_KMG};
static const int PASSED[8] = {0, 5, 10, 20, 35, 60, 100, 0};

static int evaluate(const Board &b) {
    int mg[2] = {0, 0}, eg[2] = {0, 0};
    int phase = 0;
    int bishops[2] = {0, 0};
    int nonKingMat[2] = {0, 0};
    int pawnCnt[2][8] = {{0}};
    int minRank[2][8], maxRank[2][8];
    for (int f = 0; f < 8; f++) {
        minRank[0][f] = minRank[1][f] = 8;
        maxRank[0][f] = maxRank[1][f] = -1;
    }
    for (int s = 0; s < 64; s++) {
        int p = b.sq[s];
        if (!p) continue;
        int c = pColor(p), t = pType(p);
        int idx = c == WHITE ? ((7 - (s >> 3)) * 8 + (s & 7)) : s;
        if (t == KING) {
            mg[c] += PST_KMG[idx];
            eg[c] += PST_KEG[idx];
            continue;
        }
        mg[c] += VAL[t] + PST[t][idx];
        eg[c] += VAL[t] + PST[t][idx];
        nonKingMat[c] += VAL[t];
        if (t == PAWN) {
            int f = s & 7, r = s >> 3;
            pawnCnt[c][f]++;
            if (r < minRank[c][f]) minRank[c][f] = r;
            if (r > maxRank[c][f]) maxRank[c][f] = r;
        } else if (t == KNIGHT || t == BISHOP) {
            phase += 1;
            if (t == BISHOP) bishops[c]++;
        } else if (t == ROOK) {
            phase += 2;
        } else if (t == QUEEN) {
            phase += 4;
        }
    }
    for (int c = 0; c < 2; c++) {
        if (bishops[c] >= 2) { mg[c] += 30; eg[c] += 40; }
        for (int f = 0; f < 8; f++) {
            if (pawnCnt[c][f] > 1) { mg[c] -= 12 * (pawnCnt[c][f] - 1); eg[c] -= 18 * (pawnCnt[c][f] - 1); }
            if (pawnCnt[c][f]) {
                bool iso = (f == 0 || !pawnCnt[c][f - 1]) && (f == 7 || !pawnCnt[c][f + 1]);
                if (iso) { mg[c] -= 12; eg[c] -= 14; }
            }
        }
    }
    for (int s = 0; s < 64; s++) {
        int p = b.sq[s];
        if (!p) continue;
        int c = pColor(p), t = pType(p);
        int f = s & 7, r = s >> 3;
        if (t == PAWN) {
            bool passed = true;
            for (int ff = f - 1; ff <= f + 1 && passed; ff++) {
                if (ff < 0 || ff > 7) continue;
                if (c == WHITE) { if (maxRank[BLACK][ff] > r) passed = false; }
                else { if (minRank[WHITE][ff] < r) passed = false; }
            }
            if (passed) {
                int adv = c == WHITE ? r : 7 - r;
                mg[c] += PASSED[adv] / 2;
                eg[c] += PASSED[adv];
            }
        } else if (t == ROOK) {
            if (!pawnCnt[c][f]) {
                if (!pawnCnt[c ^ 1][f]) { mg[c] += 20; eg[c] += 10; }
                else { mg[c] += 10; eg[c] += 5; }
            }
        }
    }
    if (phase > 24) phase = 24;
    int score = ((mg[0] - mg[1]) * phase + (eg[0] - eg[1]) * (24 - phase)) / 24;
    // Добивание одинокого короля: тянуть к краю, сближать королей
    for (int c = 0; c < 2; c++) {
        int o = c ^ 1;
        if (nonKingMat[o] == 0 && nonKingMat[c] >= 400) {
            int ek = b.kingSq[o], mk = b.kingSq[c];
            int ef = ek & 7, er = ek >> 3;
            int cd = std::max(3 - ef, ef - 4) + std::max(3 - er, er - 4);
            int kd = std::abs(ef - (mk & 7)) + std::abs(er - (mk >> 3));
            int bonus = cd * 12 + (14 - kd) * 5;
            score += c == WHITE ? bonus : -bonus;
        }
    }
    return (b.side == WHITE ? score : -score) + 10;
}

// ---------- поиск ----------
static const int MATE = 30000;
static const int INF = 32000;
static const int MAXPLY = 64;
enum { TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3 };

struct TTE {
    uint64_t key;
    Move move;
    int16_t score;
    int8_t depth;
    uint8_t flag;
};
static std::vector<TTE> g_tt;
static uint64_t g_ttMask = 0;

static void ttInit(int bits) {
    TTE z;
    z.key = 0; z.move = 0; z.score = 0; z.depth = 0; z.flag = 0;
    g_tt.assign((size_t)1 << bits, z);
    g_ttMask = ((uint64_t)1 << bits) - 1;
}
static void ttClear() {
    for (auto &e : g_tt) { e.key = 0; e.move = 0; e.flag = 0; e.depth = 0; e.score = 0; }
}

static inline uint32_t xrand(uint32_t &s) {
    s ^= s << 13;
    s ^= s >> 17;
    s ^= s << 5;
    return s;
}

struct Searcher {
    Board b;
    std::vector<uint64_t> path;
    Move killers[MAXPLY + 1][2];
    int hist[16][64];
    uint64_t nodes = 0;
    Uint32 start = 0, limit = 0;
    bool aborted = false;
    std::atomic<bool> *stopFlag = nullptr;
    Move rootBest = 0;
    TTE *tt = nullptr;  // своя таблица у каждого потока анализа
    uint64_t ttMask = 0;
    TTE ttDummy;

    Searcher() {
        memset(killers, 0, sizeof(killers));
        memset(hist, 0, sizeof(hist));
        memset(&ttDummy, 0, sizeof(ttDummy));
        if (!g_tt.empty()) {
            tt = g_tt.data();
            ttMask = g_ttMask;
        }
    }

    void checkTime() {
        if (stopFlag && stopFlag->load()) aborted = true;
        if (limit && SDL_GetTicks() - start >= limit) aborted = true;
    }

    bool repetition() const {
        int n = (int)path.size();
        uint64_t h = path[n - 1];
        int lim = std::min(b.half, n - 1);
        for (int i = 2; i <= lim; i += 2)
            if (path[n - 1 - i] == h) return true;
        return false;
    }

    static int toTT(int s, int ply) {
        if (s > MATE - 200) return s + ply;
        if (s < -MATE + 200) return s - ply;
        return s;
    }
    static int fromTT(int s, int ply) {
        if (s > MATE - 200) return s - ply;
        if (s < -MATE + 200) return s + ply;
        return s;
    }

    int scoreMove(Move m, Move ttm, int ply) const {
        if (m == ttm) return 4000000;
        int fl = mFlags(m);
        if (fl & F_CAP) {
            int victim = (fl & F_EP) ? PAWN : pType(b.sq[mTo(m)]);
            int att = pType(b.sq[mFrom(m)]);
            return 2000000 + VAL[victim] * 10 - VAL[att] / 10 + (mPromo(m) == QUEEN ? 50000 : 0);
        }
        if (mPromo(m)) return mPromo(m) == QUEEN ? 1900000 : -100000;
        if (m == killers[ply][0]) return 1800000;
        if (m == killers[ply][1]) return 1700000;
        return hist[b.sq[mFrom(m)]][mTo(m)];
    }

    static void pickNext(MoveList &ml, int *sc, int i) {
        int best = i;
        for (int j = i + 1; j < ml.n; j++)
            if (sc[j] > sc[best]) best = j;
        if (best != i) {
            std::swap(ml.m[i], ml.m[best]);
            std::swap(sc[i], sc[best]);
        }
    }

    int quiesce(int alpha, int beta, int ply) {
        if ((++nodes & 1023) == 0) checkTime();
        if (aborted) return 0;
        int stand = evaluate(b);
        if (ply >= MAXPLY - 1) return stand;
        if (stand >= beta) return stand;
        if (stand > alpha) alpha = stand;
        MoveList ml;
        b.gen(ml, true);
        int sc[512];
        for (int i = 0; i < ml.n; i++) sc[i] = scoreMove(ml.m[i], 0, ply);
        for (int i = 0; i < ml.n; i++) {
            pickNext(ml, sc, i);
            Move m = ml.m[i];
            if (!mPromo(m)) {
                int victim = (mFlags(m) & F_EP) ? PAWN : pType(b.sq[mTo(m)]);
                if (stand + VAL[victim] + 200 < alpha) continue;
            }
            Undo u;
            b.make(m, u);
            if (b.attacked(b.kingSq[b.side ^ 1], b.side)) {
                b.unmake(u);
                continue;
            }
            int s = -quiesce(-beta, -alpha, ply + 1);
            b.unmake(u);
            if (aborted) return 0;
            if (s >= beta) return s;
            if (s > alpha) alpha = s;
        }
        return alpha;
    }

    int negamax(int depth, int alpha, int beta, int ply, bool allowNull) {
        if ((++nodes & 1023) == 0) checkTime();
        if (aborted) return 0;
        if (ply > 0) {
            if (b.half >= 100 || repetition() || b.insufficient()) return 0;
            if (alpha < -MATE + ply) alpha = -MATE + ply;
            if (beta > MATE - ply - 1) beta = MATE - ply - 1;
            if (alpha >= beta) return alpha;
        }
        bool inChk = b.inCheck(b.side);
        if (inChk) depth++;
        if (depth <= 0) return quiesce(alpha, beta, ply);
        if (ply >= MAXPLY - 1) return evaluate(b);

        TTE &e = tt ? tt[b.hash & ttMask] : ttDummy;
        Move ttMove = 0;
        if (e.key == b.hash) {
            ttMove = e.move;
            if (ply > 0 && e.depth >= depth) {
                int s = fromTT(e.score, ply);
                if (e.flag == TT_EXACT) return s;
                if (e.flag == TT_LOWER && s >= beta) return s;
                if (e.flag == TT_UPPER && s <= alpha) return s;
            }
        }

        bool pvNode = beta - alpha > 1;
        // Нулевой ход
        if (allowNull && !pvNode && !inChk && depth >= 3 && ply > 0 && b.hasNonPawn(b.side) && evaluate(b) >= beta) {
            Undo u;
            b.makeNull(u);
            path.push_back(b.hash);
            int s = -negamax(depth - 3, -beta, -beta + 1, ply + 1, false);
            path.pop_back();
            b.unmakeNull(u);
            if (aborted) return 0;
            if (s >= beta && s < MATE - 200) return beta;
        }

        MoveList ml;
        b.gen(ml, false);
        int sc[512];
        for (int i = 0; i < ml.n; i++) sc[i] = scoreMove(ml.m[i], ttMove, ply);
        int best = -INF;
        Move bestM = 0;
        int legal = 0;
        int origAlpha = alpha;
        for (int i = 0; i < ml.n; i++) {
            pickNext(ml, sc, i);
            Move m = ml.m[i];
            Undo u;
            b.make(m, u);
            if (b.attacked(b.kingSq[b.side ^ 1], b.side)) {
                b.unmake(u);
                continue;
            }
            legal++;
            path.push_back(b.hash);
            bool quiet = !(mFlags(m) & F_CAP) && !mPromo(m);
            bool givesCheck = b.inCheck(b.side);
            int s;
            if (legal == 1) {
                s = -negamax(depth - 1, -beta, -alpha, ply + 1, true);
            } else {
                int red = 0;
                if (depth >= 3 && legal > 3 && quiet && !inChk && !givesCheck && m != killers[ply][0] &&
                    m != killers[ply][1]) {
                    red = 1;
                    if (legal > 10 && depth >= 5) red = 2;
                }
                s = -negamax(depth - 1 - red, -alpha - 1, -alpha, ply + 1, true);
                if (!aborted && s > alpha && red) s = -negamax(depth - 1, -alpha - 1, -alpha, ply + 1, true);
                if (!aborted && s > alpha && s < beta) s = -negamax(depth - 1, -beta, -alpha, ply + 1, true);
            }
            path.pop_back();
            b.unmake(u);
            if (aborted) return 0;
            if (s > best) {
                best = s;
                bestM = m;
                if (ply == 0) rootBest = m;
            }
            if (s > alpha) {
                alpha = s;
                if (alpha >= beta) {
                    if (quiet) {
                        if (killers[ply][0] != m) {
                            killers[ply][1] = killers[ply][0];
                            killers[ply][0] = m;
                        }
                        int &h = hist[b.sq[mFrom(m)]][mTo(m)];
                        h += depth * depth;
                        if (h > 1000000) {
                            for (auto &row : hist)
                                for (auto &v : row) v /= 2;
                        }
                    }
                    break;
                }
            }
        }
        if (!legal) return inChk ? -MATE + ply : 0;
        e.key = b.hash;
        e.move = bestM;
        e.score = (int16_t)toTT(best, ply);
        e.depth = (int8_t)depth;
        e.flag = best <= origAlpha ? TT_UPPER : (best >= beta ? TT_LOWER : TT_EXACT);
        return best;
    }

    Move iterate(int maxDepth) {
        Move best = 0;
        for (int d = 1; d <= maxDepth; d++) {
            rootBest = 0;
            int s = negamax(d, -INF, INF, 0, false);
            if (aborted) {
                if (rootBest && d > 1 && best == 0) best = rootBest;
                break;
            }
            best = rootBest;
            if (std::abs(s) > MATE - 100) break;
            if (limit && SDL_GetTicks() - start > limit * 45 / 100) break;
        }
        return best;
    }

    Move noisyRoot(int depth, int noise, uint32_t &rng, Move fallback) {
        MoveList ml;
        b.genLegal(ml);
        Move best = fallback ? fallback : (ml.n ? ml.m[0] : 0);
        int bestS = -INF;
        bool any = false;
        for (int i = 0; i < ml.n; i++) {
            Move m = ml.m[i];
            Undo u;
            b.make(m, u);
            path.push_back(b.hash);
            int s = -negamax(depth - 1, -INF, INF, 1, true);
            path.pop_back();
            b.unmake(u);
            if (aborted) break;
            if (noise && std::abs(s) < MATE - 500) s += (int)(xrand(rng) % (uint32_t)(2 * noise + 1)) - noise;
            if (s > bestS) {
                bestS = s;
                best = m;
                any = true;
            }
        }
        if (aborted && !any) return fallback ? fallback : best;
        if (aborted) return fallback ? fallback : best;
        return best;
    }
};

// Уровни сложности 1..5
static Move think(const Board &rb, const std::vector<uint64_t> &hist, int level, Uint32 timeMs, int gamePly,
                  uint32_t seed, std::atomic<bool> *stop) {
    Searcher *S = new Searcher();
    S->b = rb;
    S->path = hist;
    if (S->path.empty() || S->path.back() != rb.hash) S->path.push_back(rb.hash);
    S->stopFlag = stop;
    S->start = SDL_GetTicks();
    S->limit = timeMs;
    uint32_t rng = seed | 1u;
    MoveList ml;
    S->b.genLegal(ml);
    Move res = 0;
    if (ml.n == 1) {
        res = ml.m[0];
    } else if (ml.n > 1) {
        Move first = ml.m[xrand(rng) % (uint32_t)ml.n];
        switch (level) {
            case 1: res = S->noisyRoot(1, 220, rng, 0); break;
            case 2: res = S->noisyRoot(2, 90, rng, 0); break;
            case 3: {
                Move r = 0;
                for (int d = 1; d <= 3; d++) {
                    Move x = S->noisyRoot(d, 30, rng, r);
                    if (S->aborted) break;
                    r = x;
                }
                res = r;
                break;
            }
            case 4:
                if (gamePly < 6) res = S->noisyRoot(3, 14, rng, 0);
                else res = S->iterate(9);
                break;
            default:
                if (gamePly < 4) res = S->noisyRoot(3, 8, rng, 0);
                else res = S->iterate(MAXPLY - 4);
                break;
        }
        if (!res) res = first;
        // Проверка, что ход действительно легален
        bool ok = false;
        for (int i = 0; i < ml.n; i++)
            if (ml.m[i] == res) ok = true;
        if (!ok) res = ml.m[0];
    }
    delete S;
    return res;
}

// Разбор хода: лучший ход и сыгранный ход оцениваются из одной позиции
// на ОДНОЙ И ТОЙ ЖЕ глубине — так сравнение честное, без «шума» разной глубины.
struct TTBuf {
    std::vector<TTE> v;
    uint64_t mask = 0;
    void init(int bits) {
        TTE z;
        memset(&z, 0, sizeof(z));
        v.assign((size_t)1 << bits, z);
        mask = ((uint64_t)1 << bits) - 1;
    }
};
struct MoveVerdict {
    int best = 0;      // оценка лучшего хода (с точки зрения ходящего)
    int played = 0;    // оценка сыгранного хода (с той же точки зрения)
    int depth = 0;     // глубина, на которой сравнивали
    Move bestMove = 0;
    int legal = 0;     // сколько было ходов (1 — вынужденный)
};
static MoveVerdict analyseMove(const Board &pos, const std::vector<uint64_t> &hist, Move played, Uint32 timeMs,
                               std::atomic<bool> *stop, TTBuf *buf) {
    MoveVerdict r;
    Searcher *S = new Searcher();
    if (buf) {
        S->tt = buf->v.data();
        S->ttMask = buf->mask;
    }
    S->b = pos;
    S->path = hist;
    if (S->path.empty() || S->path.back() != pos.hash) S->path.push_back(pos.hash);
    S->stopFlag = stop;
    S->start = SDL_GetTicks();
    S->limit = timeMs;
    MoveList ml;
    S->b.genLegal(ml);
    r.legal = ml.n;
    if (ml.n == 0) {
        r.best = r.played = S->b.inCheck(S->b.side) ? -MATE : 0;
        delete S;
        return r;
    }
    Move bm = ml.m[0];
    int bs = 0, depth = 0;
    for (int d = 1; d <= MAXPLY - 8; d++) {
        S->rootBest = 0;
        int sc = S->negamax(d, -INF, INF, 0, false);
        if (S->aborted) break;
        bs = sc;
        depth = d;
        if (S->rootBest) bm = S->rootBest;
        if (std::abs(sc) > MATE - 100) break;
    }
    if (depth == 0) {  // не успели даже глубину 1 — хотя бы статическая оценка
        bs = evaluate(S->b);
        depth = 1;
    }
    r.best = bs;
    r.bestMove = bm;
    r.depth = depth;
    if (!played || played == bm) {
        r.played = bs;
    } else {
        // сыгранный ход: та же глубина (depth-1 после хода), полный интервал
        Undo u;
        S->b.make(played, u);
        S->path.push_back(S->b.hash);
        S->aborted = false;
        S->start = SDL_GetTicks();
        S->limit = timeMs * 2 + 200;
        int v = -evaluate(S->b);
        for (int d = 0; d <= depth - 1; d++) {
            int sc = -S->negamax(d, -INF, INF, 1, true);
            if (S->aborted) break;
            v = sc;
        }
        r.played = v;
        // поиск не идеален: если сыгранный ход вышел «лучше лучшего», он и есть лучший
        if (r.played > r.best) {
            r.best = r.played;
            r.bestMove = played;
        }
    }
    delete S;
    return r;
}

}  // namespace eng

// =====================================================================
//                           ПАРТИЯ
// =====================================================================
enum { RES_NONE = 0, RES_WHITE = 1, RES_BLACK = 2, RES_DRAW = 3 };
enum { R_NONE = 0, R_MATE, R_STALEMATE, R_RESIGN, R_TIME, R_FIFTY, R_REPEAT, R_MATERIAL, R_AGREE, R_LEFT };

struct Game {
    eng::Board cur;
    std::vector<eng::Board> before;
    std::vector<eng::Move> moves;
    std::vector<std::string> san;
    std::vector<uint64_t> hashes;
    int result = RES_NONE, reason = R_NONE, loser = -1;
    std::string startFen;  // своя начальная позиция (пусто — обычная)
    int startSide = eng::WHITE;
    int off() const { return startSide == eng::BLACK ? 1 : 0; }  // сдвиг нумерации ходов

    void reset(const std::string &fen = std::string()) {
        if (fen.empty() || !cur.setFEN(fen)) {
            cur.setStart();
            startFen.clear();
        } else {
            startFen = fen;
        }
        startSide = cur.side;
        before.clear();
        moves.clear();
        san.clear();
        hashes.assign(1, cur.hash);
        result = RES_NONE;
        reason = R_NONE;
        loser = -1;
    }
    void play(eng::Move m) {
        std::string s = eng::toSAN(cur, m);
        before.push_back(cur);
        eng::Undo u;
        cur.make(m, u);
        moves.push_back(m);
        san.push_back(s);
        hashes.push_back(cur.hash);
        evalEnd();
    }
    bool undo() {
        if (moves.empty()) return false;
        cur = before.back();
        before.pop_back();
        moves.pop_back();
        san.pop_back();
        hashes.pop_back();
        result = RES_NONE;
        reason = R_NONE;
        loser = -1;
        return true;
    }
    void evalEnd() {
        eng::MoveList ml;
        cur.genLegal(ml);
        if (ml.n == 0) {
            if (cur.inCheck(cur.side)) {
                result = cur.side == eng::WHITE ? RES_BLACK : RES_WHITE;
                reason = R_MATE;
                loser = cur.side;
            } else {
                result = RES_DRAW;
                reason = R_STALEMATE;
            }
            return;
        }
        if (cur.insufficient()) { result = RES_DRAW; reason = R_MATERIAL; return; }
        if (cur.half >= 100) { result = RES_DRAW; reason = R_FIFTY; return; }
        int cnt = 0;
        for (auto h : hashes)
            if (h == cur.hash) cnt++;
        if (cnt >= 3) { result = RES_DRAW; reason = R_REPEAT; }
    }
};

// =====================================================================
//                       РИСОВАНИЕ: ПРИМИТИВЫ
// =====================================================================
static SDL_Window *gWin = nullptr;
static SDL_Renderer *R = nullptr;
static int gW = 540, gH = 960;

struct Col {
    Uint8 r, g, b, a;
};
static Col C(int r, int g, int b, int a = 255) {
    Col c;
    c.r = (Uint8)r;
    c.g = (Uint8)g;
    c.b = (Uint8)b;
    c.a = (Uint8)a;
    return c;
}
static float clamp01(float t) { return t < 0 ? 0 : (t > 1 ? 1 : t); }
static Col mix(Col a, Col b, float t) {
    t = clamp01(t);
    return C((int)(a.r + (b.r - a.r) * t + 0.5f), (int)(a.g + (b.g - a.g) * t + 0.5f),
             (int)(a.b + (b.b - a.b) * t + 0.5f), (int)(a.a + (b.a - a.a) * t + 0.5f));
}
static Col withA(Col c, int a) {
    c.a = (Uint8)a;
    return c;
}

struct Grad {
    Col a, b;
    float x0, y0, x1, y1;
    Col at(float x, float y) const {
        float dx = x1 - x0, dy = y1 - y0;
        float L = dx * dx + dy * dy;
        if (L <= 0) return a;
        return mix(a, b, ((x - x0) * dx + (y - y0) * dy) / L);
    }
};
static Grad solid(Col c) {
    Grad g;
    g.a = c; g.b = c;
    g.x0 = g.y0 = g.x1 = g.y1 = 0;
    return g;
}
static Grad vgrad(Col top, Col bot, float y0, float y1) {
    Grad g;
    g.a = top; g.b = bot;
    g.x0 = 0; g.x1 = 0; g.y0 = y0; g.y1 = y1;
    return g;
}

typedef std::vector<SDL_FPoint> Poly;
static std::vector<SDL_Vertex> gVtx;
static std::vector<int> gIdx;

static SDL_Vertex mkV(float x, float y, Col c) {
    SDL_Vertex v;
    v.position.x = x;
    v.position.y = y;
    v.color.r = c.r;
    v.color.g = c.g;
    v.color.b = c.b;
    v.color.a = c.a;
    v.tex_coord.x = 0;
    v.tex_coord.y = 0;
    return v;
}
static SDL_FPoint P(float x, float y) {
    SDL_FPoint p;
    p.x = x;
    p.y = y;
    return p;
}

static void fillRect(float x, float y, float w, float h, Col c) {
    SDL_SetRenderDrawColor(R, c.r, c.g, c.b, c.a);
    SDL_FRect r;
    r.x = x; r.y = y; r.w = w; r.h = h;
    SDL_RenderFillRectF(R, &r);
}

static void fillConvex(const Poly &p, const Grad &g) {
    int n = (int)p.size();
    if (n < 3) return;
    gVtx.clear();
    gIdx.clear();
    for (auto &q : p) gVtx.push_back(mkV(q.x, q.y, g.at(q.x, q.y)));
    for (int i = 1; i + 1 < n; i++) {
        gIdx.push_back(0);
        gIdx.push_back(i);
        gIdx.push_back(i + 1);
    }
    SDL_RenderGeometry(R, nullptr, gVtx.data(), n, gIdx.data(), (int)gIdx.size());
}

// Триангуляция «отрезанием ушей» для невыпуклых многоугольников
static float polyArea(const Poly &p) {
    float a = 0;
    int n = (int)p.size();
    for (int i = 0, j = n - 1; i < n; j = i++) a += p[j].x * p[i].y - p[i].x * p[j].y;
    return a * 0.5f;
}
static bool insideTri(float Ax, float Ay, float Bx, float By, float Cx, float Cy, float Px, float Py) {
    float ax = Cx - Bx, ay = Cy - By, bx = Ax - Cx, by = Ay - Cy, cx = Bx - Ax, cy = By - Ay;
    float apx = Px - Ax, apy = Py - Ay, bpx = Px - Bx, bpy = Py - By, cpx = Px - Cx, cpy = Py - Cy;
    float aCb = ax * bpy - ay * bpx, cCa = cx * apy - cy * apx, bCc = bx * cpy - by * cpx;
    return aCb >= 0.0f && bCc >= 0.0f && cCa >= 0.0f;
}
static bool snip(const Poly &p, int u, int v, int w, int n, const int *V) {
    float Ax = p[V[u]].x, Ay = p[V[u]].y, Bx = p[V[v]].x, By = p[V[v]].y, Cx = p[V[w]].x, Cy = p[V[w]].y;
    if (1e-7f > ((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) return false;
    for (int k = 0; k < n; k++) {
        if (k == u || k == v || k == w) continue;
        if (insideTri(Ax, Ay, Bx, By, Cx, Cy, p[V[k]].x, p[V[k]].y)) return false;
    }
    return true;
}
static void triangulate(const Poly &p, std::vector<int> &out) {
    out.clear();
    int n = (int)p.size();
    if (n < 3) return;
    std::vector<int> V(n);
    if (polyArea(p) > 0)
        for (int i = 0; i < n; i++) V[i] = i;
    else
        for (int i = 0; i < n; i++) V[i] = n - 1 - i;
    int nv = n, count = 2 * nv;
    for (int v = nv - 1; nv > 2;) {
        if ((count--) <= 0) return;
        int u = v;
        if (nv <= u) u = 0;
        v = u + 1;
        if (nv <= v) v = 0;
        int w = v + 1;
        if (nv <= w) w = 0;
        if (snip(p, u, v, w, nv, V.data())) {
            out.push_back(V[u]);
            out.push_back(V[v]);
            out.push_back(V[w]);
            for (int s = v, t = v + 1; t < nv; s++, t++) V[s] = V[t];
            nv--;
            count = 2 * nv;
        }
    }
}
static void fillPoly(const Poly &p, const Grad &g) {
    triangulate(p, gIdx);
    if (gIdx.empty()) return;
    gVtx.clear();
    for (auto &q : p) gVtx.push_back(mkV(q.x, q.y, g.at(q.x, q.y)));
    SDL_RenderGeometry(R, nullptr, gVtx.data(), (int)gVtx.size(), gIdx.data(), (int)gIdx.size());
}

static Poly ellipseP(float cx, float cy, float rx, float ry, int n = 0) {
    if (n <= 0) n = std::max(12, std::min(72, (int)(std::max(rx, ry) * 0.9f)));
    Poly p;
    p.reserve(n);
    for (int i = 0; i < n; i++) {
        float a = (float)i / n * 6.2831853f;
        p.push_back(P(cx + std::cos(a) * rx, cy + std::sin(a) * ry));
    }
    return p;
}
static Poly rectP(float x0, float y0, float x1, float y1) {
    Poly p;
    p.push_back(P(x0, y0));
    p.push_back(P(x1, y0));
    p.push_back(P(x1, y1));
    p.push_back(P(x0, y1));
    return p;
}
static Poly rrectP(float x, float y, float w, float h, float rad) {
    rad = std::max(0.0f, std::min(rad, std::min(w, h) * 0.5f));
    if (rad < 0.5f) return rectP(x, y, x + w, y + h);
    int seg = std::max(3, std::min(10, (int)(rad / 2.5f)));
    Poly p;
    float cx[4] = {x + w - rad, x + w - rad, x + rad, x + rad};
    float cy[4] = {y + rad, y + h - rad, y + h - rad, y + rad};
    float a0[4] = {-1.5707963f, 0.0f, 1.5707963f, 3.1415926f};
    for (int c = 0; c < 4; c++)
        for (int i = 0; i <= seg; i++) {
            float a = a0[c] + 1.5707963f * i / seg;
            p.push_back(P(cx[c] + std::cos(a) * rad, cy[c] + std::sin(a) * rad));
        }
    return p;
}
static void fillRRect(float x, float y, float w, float h, float rad, const Grad &g) { fillConvex(rrectP(x, y, w, h, rad), g); }
static void fillRRect(float x, float y, float w, float h, float rad, Col c) { fillConvex(rrectP(x, y, w, h, rad), solid(c)); }
static void fillCircle(float cx, float cy, float r, Col c) { fillConvex(ellipseP(cx, cy, r, r), solid(c)); }

static void radial(float cx, float cy, float r, Col in, Col out) {
    int n = std::max(16, std::min(64, (int)r));
    gVtx.clear();
    gIdx.clear();
    gVtx.push_back(mkV(cx, cy, in));
    for (int i = 0; i < n; i++) {
        float a = (float)i / n * 6.2831853f;
        gVtx.push_back(mkV(cx + std::cos(a) * r, cy + std::sin(a) * r, out));
    }
    for (int i = 0; i < n; i++) {
        gIdx.push_back(0);
        gIdx.push_back(1 + i);
        gIdx.push_back(1 + (i + 1) % n);
    }
    SDL_RenderGeometry(R, nullptr, gVtx.data(), (int)gVtx.size(), gIdx.data(), (int)gIdx.size());
}

static void ringShape(float cx, float cy, float r0, float r1, Col c) {
    int n = std::max(20, std::min(72, (int)r1));
    gVtx.clear();
    gIdx.clear();
    for (int i = 0; i < n; i++) {
        float a = (float)i / n * 6.2831853f;
        float ca = std::cos(a), sa = std::sin(a);
        gVtx.push_back(mkV(cx + ca * r0, cy + sa * r0, c));
        gVtx.push_back(mkV(cx + ca * r1, cy + sa * r1, c));
    }
    for (int i = 0; i < n; i++) {
        int a = 2 * i, b2 = 2 * ((i + 1) % n);
        gIdx.push_back(a); gIdx.push_back(a + 1); gIdx.push_back(b2);
        gIdx.push_back(b2); gIdx.push_back(a + 1); gIdx.push_back(b2 + 1);
    }
    SDL_RenderGeometry(R, nullptr, gVtx.data(), (int)gVtx.size(), gIdx.data(), (int)gIdx.size());
}

static void thickLine(float x1, float y1, float x2, float y2, float w, Col c, bool caps = true) {
    float dx = x2 - x1, dy = y2 - y1;
    float L = std::sqrt(dx * dx + dy * dy);
    if (L < 1e-4f) {
        if (caps) fillCircle(x1, y1, w * 0.5f, c);
        return;
    }
    float nx = -dy / L * w * 0.5f, ny = dx / L * w * 0.5f;
    Poly q;
    q.push_back(P(x1 + nx, y1 + ny));
    q.push_back(P(x2 + nx, y2 + ny));
    q.push_back(P(x2 - nx, y2 - ny));
    q.push_back(P(x1 - nx, y1 - ny));
    fillConvex(q, solid(c));
    if (caps) {
        fillCircle(x1, y1, w * 0.5f, c);
        fillCircle(x2, y2, w * 0.5f, c);
    }
}

// =====================================================================
//                     ПИКСЕЛЬНЫЙ ШРИФТ 5x7
// =====================================================================
struct GlyphDef {
    uint32_t cp;
    const char *rows[7];
};
static const GlyphDef GLYPHS[] = {
    // --- русские заглавные ---
    {0x410, {".###.", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"}},  // А
    {0x411, {"#####", "#....", "#....", "####.", "#...#", "#...#", "####."}},  // Б
    {0x412, {"####.", "#...#", "#...#", "####.", "#...#", "#...#", "####."}},  // В
    {0x413, {"#####", "#....", "#....", "#....", "#....", "#....", "#...."}},  // Г
    {0x414, {"..##.", ".#.#.", ".#.#.", ".#.#.", ".#.#.", "#####", "#...#"}},  // Д
    {0x415, {"#####", "#....", "#....", "####.", "#....", "#....", "#####"}},  // Е
    {0x401, {".#.#.", ".....", "#####", "#....", "####.", "#....", "#####"}},  // Ё
    {0x416, {"#.#.#", "#.#.#", ".###.", "..#..", ".###.", "#.#.#", "#.#.#"}},  // Ж
    {0x417, {".###.", "#...#", "....#", "..##.", "....#", "#...#", ".###."}},  // З
    {0x418, {"#...#", "#...#", "#..##", "#.#.#", "##..#", "#...#", "#...#"}},  // И
    {0x419, {".#.#.", "..#..", "#...#", "#..##", "#.#.#", "##..#", "#...#"}},  // Й
    {0x41A, {"#...#", "#..#.", "#.#..", "##...", "#.#..", "#..#.", "#...#"}},  // К
    {0x41B, {"..###", ".#..#", ".#..#", ".#..#", ".#..#", ".#..#", "#...#"}},  // Л
    {0x41C, {"#...#", "##.##", "#.#.#", "#.#.#", "#...#", "#...#", "#...#"}},  // М
    {0x41D, {"#...#", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"}},  // Н
    {0x41E, {".###.", "#...#", "#...#", "#...#", "#...#", "#...#", ".###."}},  // О
    {0x41F, {"#####", "#...#", "#...#", "#...#", "#...#", "#...#", "#...#"}},  // П
    {0x420, {"####.", "#...#", "#...#", "####.", "#....", "#....", "#...."}},  // Р
    {0x421, {".###.", "#...#", "#....", "#....", "#....", "#...#", ".###."}},  // С
    {0x422, {"#####", "..#..", "..#..", "..#..", "..#..", "..#..", "..#.."}},  // Т
    {0x423, {"#...#", "#...#", "#...#", ".####", "....#", "#...#", ".###."}},  // У
    {0x424, {"..#..", ".###.", "#.#.#", "#.#.#", "#.#.#", ".###.", "..#.."}},  // Ф
    {0x425, {"#...#", "#...#", ".#.#.", "..#..", ".#.#.", "#...#", "#...#"}},  // Х
    {0x426, {"#..#.", "#..#.", "#..#.", "#..#.", "#..#.", "#####", "....#"}},  // Ц
    {0x427, {"#...#", "#...#", "#...#", ".####", "....#", "....#", "....#"}},  // Ч
    {0x428, {"#.#.#", "#.#.#", "#.#.#", "#.#.#", "#.#.#", "#.#.#", "#####"}},  // Ш
    {0x429, {"#.#.#", "#.#.#", "#.#.#", "#.#.#", "#.#.#", "#####", "....#"}},  // Щ
    {0x42A, {"##...", ".#...", ".#...", ".###.", ".#..#", ".#..#", ".###."}},  // Ъ
    {0x42B, {"#...#", "#...#", "#...#", "##..#", "#.#.#", "#.#.#", "##..#"}},  // Ы
    {0x42C, {"#....", "#....", "#....", "####.", "#...#", "#...#", "####."}},  // Ь
    {0x42D, {".###.", "#...#", "....#", ".####", "....#", "#...#", ".###."}},  // Э
    {0x42E, {"#..#.", "#.#.#", "#.#.#", "###.#", "#.#.#", "#.#.#", "#..#."}},  // Ю
    {0x42F, {".####", "#...#", "#...#", ".####", "..#.#", ".#..#", "#...#"}},  // Я
    {0x440, {".....", ".....", "####.", "#...#", "####.", "#....", "#...."}},  // р (для «Кр»)
    // --- цифры ---
    {'0', {".###.", "#...#", "#..##", "#.#.#", "##..#", "#...#", ".###."}},
    {'1', {"..#..", ".##..", "..#..", "..#..", "..#..", "..#..", ".###."}},
    {'2', {".###.", "#...#", "....#", "...#.", "..#..", ".#...", "#####"}},
    {'3', {"#####", "...#.", "..#..", "...#.", "....#", "#...#", ".###."}},
    {'4', {"...#.", "..##.", ".#.#.", "#..#.", "#####", "...#.", "...#."}},
    {'5', {"#####", "#....", "####.", "....#", "....#", "#...#", ".###."}},
    {'6', {"..##.", ".#...", "#....", "####.", "#...#", "#...#", ".###."}},
    {'7', {"#####", "....#", "...#.", "..#..", ".#...", ".#...", ".#..."}},
    {'8', {".###.", "#...#", "#...#", ".###.", "#...#", "#...#", ".###."}},
    {'9', {".###.", "#...#", "#...#", ".####", "....#", "...#.", ".##.."}},
    // --- латиница для обозначения полей ---
    {'a', {".....", ".....", ".###.", "....#", ".####", "#...#", ".####"}},
    {'b', {"#....", "#....", "####.", "#...#", "#...#", "#...#", "####."}},
    {'c', {".....", ".....", ".###.", "#....", "#....", "#...#", ".###."}},
    {'d', {"....#", "....#", ".####", "#...#", "#...#", "#...#", ".####"}},
    {'e', {".....", ".....", ".###.", "#...#", "#####", "#....", ".###."}},
    {'f', {"..##.", ".#...", ".#...", "###..", ".#...", ".#...", ".#..."}},
    {'g', {".....", ".....", ".####", "#...#", ".####", "....#", "####."}},
    {'h', {"#....", "#....", "####.", "#...#", "#...#", "#...#", "#...#"}},
    {'x', {".....", ".....", "#...#", ".#.#.", "..#..", ".#.#.", "#...#"}},
    // --- знаки ---
    {'+', {".....", "..#..", "..#..", "#####", "..#..", "..#..", "....."}},
    {'#', {".#.#.", ".#.#.", "#####", ".#.#.", "#####", ".#.#.", ".#.#."}},
    {'-', {".....", ".....", ".....", "####.", ".....", ".....", "....."}},
    {'=', {".....", ".....", "####.", ".....", "####.", ".....", "....."}},
    {'.', {".....", ".....", ".....", ".....", ".....", "##...", "##..."}},
    {',', {".....", ".....", ".....", ".....", "##...", ".#...", "#...."}},
    {'>', {".....", "#....", ".#...", "..#..", ".#...", "#....", "....."}},
    {'<', {".....", "..#..", ".#...", "#....", ".#...", "..#..", "....."}},
    {';', {".....", "##...", "##...", ".....", "##...", ".#...", "#...."}},
    {':', {".....", "##...", "##...", ".....", "##...", "##...", "....."}},
    {'!', {"#....", "#....", "#....", "#....", "#....", ".....", "#...."}},
    {'?', {".###.", "#...#", "....#", "...#.", "..#..", ".....", "..#.."}},
    {'(', {".#...", "#....", "#....", "#....", "#....", "#....", ".#..."}},
    {')', {"#....", ".#...", ".#...", ".#...", ".#...", ".#...", "#...."}},
    {'/', {"....#", "....#", "...#.", "..#..", ".#...", "#....", "#...."}},
    {'%', {"##..#", "##..#", "...#.", "..#..", ".#...", "#..##", "#..##"}},
    {'\'', {"#....", "#....", ".....", ".....", ".....", ".....", "....."}},
    {0xB7, {".....", ".....", ".....", "##...", "##...", ".....", "....."}},  // ·
    {0x2026, {".....", ".....", ".....", ".....", ".....", ".....", "#.#.#"}},  // …
};

struct Glyph {
    uint8_t rows[7];
    int w;
    bool ok;
};
static Glyph gAscii[128];
static Glyph gCyr[96];  // U+0400..U+045F
static Glyph gMisc[2];  // · и …

static void fontInit() {
    for (auto &g : gAscii) g.ok = false;
    for (auto &g : gCyr) g.ok = false;
    for (auto &g : gMisc) g.ok = false;
    for (const auto &d : GLYPHS) {
        Glyph g;
        g.ok = true;
        int maxc = 0;
        for (int r = 0; r < 7; r++) {
            uint8_t bits = 0;
            for (int c = 0; c < 5; c++)
                if (d.rows[r][c] == '#') {
                    bits |= (uint8_t)(1 << c);
                    if (c + 1 > maxc) maxc = c + 1;
                }
            g.rows[r] = bits;
        }
        bool alnum = (d.cp >= '0' && d.cp <= '9') || (d.cp >= 'a' && d.cp <= 'z') || d.cp >= 0x400;
        g.w = alnum && d.cp < 0x2000 ? 5 : std::max(1, maxc);
        if (d.cp == '+' || d.cp == '#' || d.cp == '?' || d.cp == '/' || d.cp == '%' || d.cp == 0x2026) g.w = 5;
        if (d.cp < 128) gAscii[d.cp] = g;
        else if (d.cp >= 0x400 && d.cp < 0x460) gCyr[d.cp - 0x400] = g;
        else if (d.cp == 0xB7) gMisc[0] = g;
        else if (d.cp == 0x2026) gMisc[1] = g;
    }
}

static const Glyph *glyphFor(uint32_t cp) {
    if (cp >= 'A' && cp <= 'Z' && !gAscii[cp].ok) cp = cp - 'A' + 'a';
    if (cp < 128) return gAscii[cp].ok ? &gAscii[cp] : &gAscii[(int)'?'];
    if (cp == 0x451) cp = 0x401;
    if (cp >= 0x430 && cp < 0x450 && !gCyr[cp - 0x400].ok) cp -= 0x20;
    if (cp >= 0x400 && cp < 0x460 && gCyr[cp - 0x400].ok) return &gCyr[cp - 0x400];
    if (cp == 0x2013 || cp == 0x2014) return &gAscii[(int)'-'];
    if (cp == 0xB7) return &gMisc[0];
    if (cp == 0x2026) return &gMisc[1];
    return &gAscii[(int)'?'];
}

static std::vector<uint32_t> utf8(const std::string &s) {
    std::vector<uint32_t> out;
    size_t i = 0;
    while (i < s.size()) {
        unsigned char c = (unsigned char)s[i];
        uint32_t cp;
        int n;
        if (c < 0x80) { cp = c; n = 1; }
        else if ((c >> 5) == 6) { cp = c & 0x1F; n = 2; }
        else if ((c >> 4) == 14) { cp = c & 0x0F; n = 3; }
        else { cp = c & 0x07; n = 4; }
        for (int k = 1; k < n && i + k < s.size(); k++) cp = (cp << 6) | ((unsigned char)s[i + k] & 0x3F);
        i += n;
        out.push_back(cp);
    }
    return out;
}

static int textW(const std::string &s, int sc) {
    auto cps = utf8(s);
    int w = 0;
    for (uint32_t cp : cps) w += (cp == ' ' ? 3 : glyphFor(cp)->w) + 1;
    if (w > 0) w -= 1;
    return w * sc;
}
static int textH(int sc) { return 7 * sc; }

static std::vector<SDL_FRect> gRects;
static void textRaw(const std::vector<uint32_t> &cps, float x, float y, int sc, Col c) {
    gRects.clear();
    float cx = std::floor(x + 0.5f);
    float cy = std::floor(y + 0.5f);
    for (uint32_t cp : cps) {
        if (cp == ' ') { cx += 4 * sc; continue; }
        const Glyph *g = glyphFor(cp);
        for (int r = 0; r < 7; r++) {
            uint8_t bits = g->rows[r];
            int c0 = 0;
            while (c0 < 5) {
                if (bits & (1 << c0)) {
                    int c1 = c0;
                    while (c1 + 1 < 5 && (bits & (1 << (c1 + 1)))) c1++;
                    SDL_FRect rc;
                    rc.x = cx + c0 * sc;
                    rc.y = cy + r * sc;
                    rc.w = (float)((c1 - c0 + 1) * sc);
                    rc.h = (float)sc;
                    gRects.push_back(rc);
                    c0 = c1 + 1;
                } else {
                    c0++;
                }
            }
        }
        cx += (g->w + 1) * sc;
    }
    if (gRects.empty()) return;
    SDL_SetRenderDrawColor(R, c.r, c.g, c.b, c.a);
    SDL_RenderFillRectsF(R, gRects.data(), (int)gRects.size());
}

// align: 0 — влево, 1 — по центру, 2 — вправо; y — верх строки
static void text(const std::string &s, float x, float y, int sc, Col c, int align = 0, bool shadow = true) {
    if (sc < 1) sc = 1;
    auto cps = utf8(s);
    int w = textW(s, sc);
    if (align == 1) x -= w * 0.5f;
    else if (align == 2) x -= w;
    if (shadow) {
        float o = (float)std::max(1, sc / 2);
        textRaw(cps, x + o, y + o, sc, C(0, 0, 0, (int)(c.a * 0.45f)));
    }
    textRaw(cps, x, y, sc, c);
}
static int fitScale(const std::string &s, float maxW, int pref) {
    int sc = pref;
    while (sc > 1 && textW(s, sc) > maxW) sc--;
    return sc;
}

// =====================================================================
//                           ФИГУРЫ
// =====================================================================
struct PLine { float x1, y1, x2, y2, w; };
struct PDot { float x, y, r; };
struct PieceGeo {
    std::vector<Poly> polys;
    std::vector<PLine> lines;
    std::vector<PDot> dots;
};
static PieceGeo gGeo[7];

static Poly polyL(std::initializer_list<float> v) {
    Poly p;
    const float *a = v.begin();
    for (size_t i = 0; i + 1 < v.size(); i += 2) p.push_back(P(a[i], a[i + 1]));
    return p;
}

static void geoInit() {
    // Пешка
    {
        PieceGeo &g = gGeo[eng::PAWN];
        g.polys.push_back(rrectP(0.22f, 0.79f, 0.56f, 0.11f, 0.035f));
        g.polys.push_back(polyL({0.37f, 0.60f, 0.63f, 0.60f, 0.72f, 0.80f, 0.28f, 0.80f}));
        g.polys.push_back(ellipseP(0.5f, 0.60f, 0.19f, 0.045f, 40));
        g.polys.push_back(polyL({0.43f, 0.46f, 0.57f, 0.46f, 0.61f, 0.60f, 0.39f, 0.60f}));
        g.polys.push_back(ellipseP(0.5f, 0.37f, 0.14f, 0.14f, 48));
        g.lines.push_back({0.27f, 0.80f, 0.73f, 0.80f, 0.022f});
    }
    // Ладья
    {
        PieceGeo &g = gGeo[eng::ROOK];
        g.polys.push_back(rrectP(0.18f, 0.80f, 0.64f, 0.10f, 0.035f));
        g.polys.push_back(rectP(0.24f, 0.72f, 0.76f, 0.81f));
        g.polys.push_back(polyL({0.32f, 0.37f, 0.68f, 0.37f, 0.71f, 0.73f, 0.29f, 0.73f}));
        g.polys.push_back(rectP(0.23f, 0.27f, 0.77f, 0.38f));
        g.polys.push_back(rectP(0.23f, 0.14f, 0.36f, 0.28f));
        g.polys.push_back(rectP(0.435f, 0.14f, 0.565f, 0.28f));
        g.polys.push_back(rectP(0.64f, 0.14f, 0.77f, 0.28f));
        g.lines.push_back({0.26f, 0.38f, 0.74f, 0.38f, 0.022f});
        g.lines.push_back({0.27f, 0.725f, 0.73f, 0.725f, 0.022f});
        g.lines.push_back({0.21f, 0.81f, 0.79f, 0.81f, 0.022f});
    }
    // Конь
    {
        PieceGeo &g = gGeo[eng::KNIGHT];
        g.polys.push_back(rrectP(0.20f, 0.80f, 0.60f, 0.10f, 0.035f));
        g.polys.push_back(polyL({0.27f, 0.81f, 0.29f, 0.68f, 0.33f, 0.61f, 0.42f, 0.54f, 0.34f, 0.53f, 0.23f, 0.56f,
                                 0.165f, 0.51f, 0.155f, 0.45f, 0.20f, 0.39f, 0.30f, 0.29f, 0.35f, 0.21f, 0.39f, 0.10f,
                                 0.45f, 0.19f, 0.56f, 0.21f, 0.68f, 0.30f, 0.77f, 0.46f, 0.79f, 0.64f, 0.76f, 0.81f}));
        g.lines.push_back({0.22f, 0.81f, 0.78f, 0.81f, 0.022f});
        g.lines.push_back({0.50f, 0.25f, 0.62f, 0.31f, 0.024f});
        g.lines.push_back({0.62f, 0.31f, 0.70f, 0.44f, 0.024f});
        g.lines.push_back({0.70f, 0.44f, 0.72f, 0.60f, 0.024f});
        g.lines.push_back({0.19f, 0.525f, 0.26f, 0.515f, 0.018f});
        g.dots.push_back({0.355f, 0.33f, 0.030f});
        g.dots.push_back({0.205f, 0.455f, 0.016f});
    }
    // Слон
    {
        PieceGeo &g = gGeo[eng::BISHOP];
        g.polys.push_back(rrectP(0.22f, 0.81f, 0.56f, 0.09f, 0.035f));
        g.polys.push_back(polyL({0.37f, 0.69f, 0.63f, 0.69f, 0.71f, 0.82f, 0.29f, 0.82f}));
        g.polys.push_back(ellipseP(0.5f, 0.685f, 0.19f, 0.045f, 40));
        Poly mitre;
        for (int i = 0; i <= 24; i++) {
            float a = 3.1415926f * i / 24.0f;  // нижняя половина
            mitre.push_back(P(0.5f + std::cos(a) * 0.17f, 0.50f + std::sin(a) * 0.15f));
        }
        for (int i = 1; i < 12; i++) {
            float t = (float)i / 12.0f;
            float x = 0.33f + t * 0.17f;
            float y = 0.50f - std::sin(t * 1.5707963f) * 0.26f;
            mitre.push_back(P(x, y));
        }
        mitre.push_back(P(0.5f, 0.235f));
        for (int i = 11; i >= 1; i--) {
            float t = (float)i / 12.0f;
            float x = 0.67f - t * 0.17f;
            float y = 0.50f - std::sin(t * 1.5707963f) * 0.26f;
            mitre.push_back(P(x, y));
        }
        g.polys.push_back(mitre);
        g.polys.push_back(ellipseP(0.5f, 0.205f, 0.055f, 0.055f, 32));
        g.lines.push_back({0.455f, 0.36f, 0.565f, 0.47f, 0.035f});
        g.lines.push_back({0.33f, 0.62f, 0.67f, 0.62f, 0.022f});
        g.lines.push_back({0.25f, 0.82f, 0.75f, 0.82f, 0.022f});
    }
    // Ферзь
    {
        PieceGeo &g = gGeo[eng::QUEEN];
        g.polys.push_back(rrectP(0.18f, 0.81f, 0.64f, 0.09f, 0.035f));
        g.polys.push_back(ellipseP(0.5f, 0.80f, 0.255f, 0.045f, 40));
        g.polys.push_back(polyL({0.30f, 0.80f, 0.70f, 0.80f, 0.85f, 0.33f, 0.70f, 0.55f, 0.67f, 0.27f, 0.58f, 0.53f,
                                 0.50f, 0.22f, 0.42f, 0.53f, 0.33f, 0.27f, 0.30f, 0.55f, 0.15f, 0.33f}));
        g.polys.push_back(ellipseP(0.15f, 0.31f, 0.055f, 0.055f, 28));
        g.polys.push_back(ellipseP(0.33f, 0.245f, 0.055f, 0.055f, 28));
        g.polys.push_back(ellipseP(0.50f, 0.20f, 0.06f, 0.06f, 28));
        g.polys.push_back(ellipseP(0.67f, 0.245f, 0.055f, 0.055f, 28));
        g.polys.push_back(ellipseP(0.85f, 0.31f, 0.055f, 0.055f, 28));
        g.lines.push_back({0.30f, 0.67f, 0.70f, 0.67f, 0.024f});
        g.lines.push_back({0.21f, 0.82f, 0.79f, 0.82f, 0.022f});
    }
    // Король
    {
        PieceGeo &g = gGeo[eng::KING];
        g.polys.push_back(rrectP(0.18f, 0.81f, 0.64f, 0.09f, 0.035f));
        g.polys.push_back(ellipseP(0.5f, 0.80f, 0.255f, 0.045f, 40));
        g.polys.push_back(polyL({0.26f, 0.45f, 0.74f, 0.45f, 0.68f, 0.80f, 0.32f, 0.80f}));
        g.polys.push_back(ellipseP(0.5f, 0.45f, 0.255f, 0.07f, 48));
        g.polys.push_back(ellipseP(0.5f, 0.40f, 0.15f, 0.095f, 40));
        g.polys.push_back(rectP(0.462f, 0.09f, 0.538f, 0.33f));
        g.polys.push_back(rectP(0.39f, 0.15f, 0.61f, 0.22f));
        g.lines.push_back({0.31f, 0.60f, 0.69f, 0.60f, 0.024f});
        g.lines.push_back({0.27f, 0.47f, 0.73f, 0.47f, 0.022f});
        g.lines.push_back({0.21f, 0.82f, 0.79f, 0.82f, 0.022f});
    }
}

static Poly xform(const Poly &p, float x, float y, float s, float ox, float oy) {
    Poly q;
    q.reserve(p.size());
    for (auto &a : p) q.push_back(P(x + a.x * s + ox, y + a.y * s + oy));
    return q;
}

static void drawPieceShape(int color, int type, float x, float y, float s, bool shadow) {
    const PieceGeo &G = gGeo[type];
    bool white = color == eng::WHITE;
    Col outline = white ? C(38, 30, 24) : C(6, 6, 8);
    Col detail = white ? C(70, 56, 44) : C(176, 176, 182);
    Col light = white ? C(255, 253, 244) : C(104, 104, 112);
    Col dark = white ? C(200, 188, 166) : C(22, 22, 26);
    if (shadow) fillConvex(ellipseP(x + 0.52f * s, y + 0.885f * s, 0.36f * s, 0.07f * s), solid(C(0, 0, 0, 55)));
    float ot = s * 0.042f;
    for (int k = 0; k < 16; k++) {
        float a = k * 6.2831853f / 16.0f;
        float ox = std::cos(a) * ot, oy = std::sin(a) * ot;
        for (auto &p : G.polys) fillPoly(xform(p, x, y, s, ox, oy), solid(outline));
    }
    Grad g;
    g.a = light;
    g.b = dark;
    g.x0 = x + 0.22f * s;
    g.y0 = y + 0.12f * s;
    g.x1 = x + 0.82f * s;
    g.y1 = y + 0.95f * s;
    for (auto &p : G.polys) fillPoly(xform(p, x, y, s, 0, 0), g);
    for (auto &l : G.lines) thickLine(x + l.x1 * s, y + l.y1 * s, x + l.x2 * s, y + l.y2 * s, l.w * s, detail);
    for (auto &d : G.dots) fillCircle(x + d.x * s, y + d.y * s, d.r * s, detail);
}

// ---------- классические фигуры (векторные) ----------
// Контуры повторяют свободный набор шахматных фигур Colin M.L. Burnett
// (Wikimedia Commons, лицензии BSD / GPL / GFDL). Поле 45x45 единиц,
// заливка + обводка 1.5, растеризация в коде со сглаживанием.
struct VPt {
    float x, y;
};
struct VSub {
    std::vector<VPt> p;
    bool closed;
};
struct VShape {
    const char *d;
    char fill;    // 'W' белый, 'B' чёрный, 'L' светло-серый, 0 — нет
    char stroke;  // то же
    float sw;     // толщина обводки
    bool roundCap;
    bool useM;
    float m[6];   // матрица (a,b,c,d,e,f) как в SVG
};
#define VS(d, f, s, w, rc) {d, f, s, w, rc, false, {1, 0, 0, 1, 0, 0}}

static const char *VP_PAWN =
    "m 22.5,9 c -2.21,0 -4,1.79 -4,4 0,0.89 0.29,1.71 0.78,2.38 C 17.33,16.5 16,18.59 16,21 c 0,2.03 0.94,3.84 "
    "2.41,5.03 C 15.41,27.09 11,31.58 11,39.5 H 34 C 34,31.58 29.59,27.09 26.59,26.03 28.06,24.84 29,23.03 29,21 "
    "29,18.59 27.67,16.5 25.72,15.38 26.21,14.71 26.5,13.89 26.5,13 c 0,-2.21 -1.79,-4 -4,-4 z";
static const char *VP_N_BODY = "M 22,10 C 32.5,11 38.5,18 38,39 L 15,39 C 15,30 25,32.5 23,18";
static const char *VP_N_HEAD =
    "M 24,18 C 24.38,20.91 18.45,25.37 16,27 C 13,29 13.18,31.34 11,31 C 9.958,30.06 12.41,27.96 11,28 C 10,28 "
    "11.19,29.23 10,30 C 9,30 5.997,31 6,26 C 6,24 12,14 12,14 C 12,14 13.89,12.1 14,10.5 C 13.27,9.506 13.5,8.5 "
    "13.5,7.5 C 14.5,6.5 16.5,10 16.5,10 L 18.5,10 C 18.5,10 19.28,8.008 21,7 C 22,7 22,10 22,10";
static const char *VP_N_NOSE = "M 9.5 25.5 A 0.5 0.5 0 1 1 8.5,25.5 A 0.5 0.5 0 1 1 9.5 25.5 z";
static const char *VP_N_EYE = "M 15 15.5 A 0.5 1.5 0 1 1 14,15.5 A 0.5 1.5 0 1 1 15 15.5 z";
static const char *VP_N_MANE =
    "M 24.55,10.4 L 24.1,11.85 L 24.6,12 C 27.75,13 30.25,14.49 32.5,18.75 C 34.75,23.01 35.75,29.06 35.25,39 "
    "L 35.2,39.5 L 37.45,39.5 L 37.5,39 C 38,28.94 36.62,22.15 34.25,17.66 C 31.88,13.17 28.46,11.02 25.06,10.5 "
    "L 24.55,10.4 z";
static const char *VP_B_BASE =
    "M 9,36 C 12.39,35.03 19.11,36.43 22.5,34 C 25.89,36.43 32.61,35.03 36,36 C 36,36 37.65,36.54 39,38 C 38.32,"
    "38.97 37.35,38.99 36,38.5 C 32.61,37.53 25.89,38.96 22.5,37.5 C 19.11,38.96 12.39,37.53 9,38.5 C 7.65,38.99 "
    "6.68,38.97 6,38 C 7.35,36.54 9,36 9,36 z";
static const char *VP_B_BODY =
    "M 15,32 C 17.5,34.5 27.5,34.5 30,32 C 30.5,30.5 30,30 30,30 C 30,27.5 27.5,26 27.5,26 C 33,24.5 33.5,14.5 "
    "22.5,10.5 C 11.5,14.5 12,24.5 17.5,26 C 17.5,26 15,27.5 15,30 C 15,30 14.5,30.5 15,32 z";
static const char *VP_B_BALL = "M 25 8 A 2.5 2.5 0 1 1 20,8 A 2.5 2.5 0 1 1 25 8 z";
static const char *VP_B_LINES = "M 17.5,26 L 27.5,26 M 15,30 L 30,30 M 22.5,15.5 L 22.5,20.5 M 20,18 L 25,18";
static const char *VP_R_BASE = "M 9,39 L 36,39 L 36,36 L 9,36 L 9,39 z";
static const char *VP_R_BASE2 = "M 12,36 L 12,32 L 33,32 L 33,36 L 12,36 z";
static const char *VP_R_TOP = "M 11,14 L 11,9 L 15,9 L 15,11 L 20,11 L 20,9 L 25,9 L 25,11 L 30,11 L 30,9 L 34,9 L 34,14";
static const char *VP_Q_CROWN =
    "M 9,26 C 17.5,24.5 30,24.5 36,26 L 38.5,13.5 L 31,25 L 30.7,10.9 L 25.5,24.5 L 22.5,10 L 19.5,24.5 L 14.3,"
    "10.9 L 14,25 L 6.5,13.5 L 9,26 z";
static const char *VP_Q_BODY =
    "M 9,26 C 9,28 10.5,28 11.5,30 C 12.5,31.5 12.5,31 12,33.5 C 10.5,34.5 11,36 11,36 C 9.5,37.5 11,38.5 11,"
    "38.5 C 17.5,39.5 27.5,39.5 34,38.5 C 34,38.5 35.5,37.5 34,36 C 34,36 34.5,34.5 33,33.5 C 32.5,31 32.5,31.5 "
    "33.5,30 C 34.5,28 36,28 36,26 C 27.5,24.5 17.5,24.5 9,26 z";
static const char *VP_Q_BALLS =
    "M 8,12 A 2,2 0 1 1 4,12 A 2,2 0 1 1 8,12 z M 16,9 A 2,2 0 1 1 12,9 A 2,2 0 1 1 16,9 z "
    "M 24.5,8 A 2,2 0 1 1 20.5,8 A 2,2 0 1 1 24.5,8 z M 33,9 A 2,2 0 1 1 29,9 A 2,2 0 1 1 33,9 z "
    "M 41,12 A 2,2 0 1 1 37,12 A 2,2 0 1 1 41,12 z";
static const char *VP_K_CROSS = "M 22.5,11.63 L 22.5,6 M 20,8 L 25,8";
static const char *VP_K_TOP =
    "M 22.5,25 C 22.5,25 27,17.5 25.5,14.5 C 25.5,14.5 24.5,12 22.5,12 C 20.5,12 19.5,14.5 19.5,14.5 C 18,17.5 "
    "22.5,25 22.5,25";
static const char *VP_K_BODY =
    "M 12.5,37 C 18,40.5 27,40.5 32.5,37 L 32.5,30 C 32.5,30 41.5,25.5 38.5,19.5 C 34.5,13 25,16 22.5,23.5 L "
    "22.5,27 L 22.5,23.5 C 20,16 10.5,13 6.5,19.5 C 3.5,25.5 12.5,30 12.5,30 L 12.5,37";
static const char *VP_K_BANDS =
    "M 12.5,30 C 18,27 27,27 32.5,30 M 12.5,33.5 C 18,30.5 27,30.5 32.5,33.5 M 12.5,37 C 18,34 27,34 32.5,37";

// Набор фигур: [цвет][тип], смещение группы по y (как в оригинале)
struct VPiece {
    std::vector<VShape> shapes;
    float dy;
};
static VPiece gVP[2][7];

static void vpiecesInit() {
    const float EYE_M[6] = {0.866f, 0.5f, -0.5f, 0.866f, 9.693f, -5.173f};
    auto eye = [&](char col) {
        VShape s = VS(VP_N_EYE, col, col, 1.5f, true);
        s.useM = true;
        for (int i = 0; i < 6; i++) s.m[i] = EYE_M[i];
        return s;
    };
    // белые
    gVP[0][eng::PAWN] = {{VS(VP_PAWN, 'W', 'B', 1.5f, true)}, 0};
    gVP[0][eng::KNIGHT] = {{VS(VP_N_BODY, 'W', 'B', 1.5f, true), VS(VP_N_HEAD, 'W', 'B', 1.5f, true),
                            VS(VP_N_NOSE, 'B', 'B', 1.5f, true), eye('B')}, 0.3f};
    gVP[0][eng::BISHOP] = {{VS(VP_B_BASE, 'W', 'B', 1.5f, false), VS(VP_B_BODY, 'W', 'B', 1.5f, false),
                            VS(VP_B_BALL, 'W', 'B', 1.5f, false), VS(VP_B_LINES, 0, 'B', 1.5f, true)}, 0.6f};
    gVP[0][eng::ROOK] = {{VS(VP_R_BASE, 'W', 'B', 1.5f, false), VS(VP_R_BASE2, 'W', 'B', 1.5f, false),
                          VS(VP_R_TOP, 'W', 'B', 1.5f, false), VS("M 34,14 L 31,17 L 14,17 L 11,14", 'W', 'B', 1.5f, true),
                          VS("M 31,17 L 31,29.5 L 14,29.5 L 14,17", 'W', 'B', 1.5f, false),
                          VS("M 31,29.5 L 32.5,32 L 12.5,32 L 14,29.5", 'W', 'B', 1.5f, true),
                          VS("M 11,14 L 34,14", 0, 'B', 1.5f, true)}, 0.3f};
    gVP[0][eng::QUEEN] = {{VS(VP_Q_CROWN, 'W', 'B', 1.5f, false), VS(VP_Q_BODY, 'W', 'B', 1.5f, false),
                           VS("M 11.5,30 C 15,29 30,29 33.5,30", 0, 'B', 1.5f, false),
                           VS("M 12,33.5 C 18,32.5 27,32.5 33,33.5", 0, 'B', 1.5f, false),
                           VS(VP_Q_BALLS, 'W', 'B', 1.5f, false)}, 0};
    gVP[0][eng::KING] = {{VS(VP_K_CROSS, 0, 'B', 1.5f, true), VS(VP_K_TOP, 'W', 'B', 1.5f, false),
                          VS(VP_K_BODY, 'W', 'B', 1.5f, true), VS(VP_K_BANDS, 0, 'B', 1.5f, true)}, 0};
    // чёрные
    gVP[1][eng::PAWN] = {{VS(VP_PAWN, 'B', 'B', 1.5f, true)}, 0};
    gVP[1][eng::KNIGHT] = {{VS(VP_N_BODY, 'B', 'B', 1.5f, true), VS(VP_N_HEAD, 'B', 'B', 1.5f, true),
                            VS(VP_N_NOSE, 'L', 'L', 1.5f, true), eye('L'), VS(VP_N_MANE, 'L', 0, 0, false)}, 0.3f};
    gVP[1][eng::BISHOP] = {{VS(VP_B_BASE, 'B', 'B', 1.5f, false), VS(VP_B_BODY, 'B', 'B', 1.5f, false),
                            VS(VP_B_BALL, 'B', 'B', 1.5f, false), VS(VP_B_LINES, 0, 'W', 1.5f, true)}, 0.6f};
    gVP[1][eng::ROOK] = {{VS(VP_R_BASE, 'B', 'B', 1.5f, false),
                          VS("M 12.5,32 L 14,29.5 L 31,29.5 L 32.5,32 L 12.5,32 z", 'B', 'B', 1.5f, false),
                          VS(VP_R_BASE2, 'B', 'B', 1.5f, false),
                          VS("M 14,29.5 L 14,16.5 L 31,16.5 L 31,29.5 L 14,29.5 z", 'B', 'B', 1.5f, false),
                          VS("M 14,16.5 L 11,14 L 34,14 L 31,16.5 L 14,16.5 z", 'B', 'B', 1.5f, false),
                          VS("M 11,14 L 11,9 L 15,9 L 15,11 L 20,11 L 20,9 L 25,9 L 25,11 L 30,11 L 30,9 L 34,9 L 34,14 L 11,14 z", 'B', 'B', 1.5f, false),
                          VS("M 12,35.5 L 33,35.5", 0, 'W', 1.0f, false), VS("M 13,31.5 L 32,31.5", 0, 'W', 1.0f, false),
                          VS("M 14,29.5 L 31,29.5", 0, 'W', 1.0f, false), VS("M 14,16.5 L 31,16.5", 0, 'W', 1.0f, false),
                          VS("M 11,14 L 34,14", 0, 'W', 1.0f, false)}, 0.3f};
    gVP[1][eng::QUEEN] = {{VS(VP_Q_CROWN, 'B', 'B', 1.5f, false), VS(VP_Q_BODY, 'B', 'B', 1.5f, true),
                           VS(VP_Q_BALLS, 'B', 'B', 1.5f, true),
                           VS("M 11,38.5 A 35,35 1 0 0 34,38.5", 0, 'B', 1.5f, false),
                           VS("M 11,29 A 35,35 1 0 1 34,29", 0, 'W', 1.5f, true),
                           VS("M 12.5,31.5 L 32.5,31.5", 0, 'W', 1.5f, true),
                           VS("M 11.5,34.5 A 35,35 1 0 0 33.5,34.5", 0, 'W', 1.5f, true),
                           VS("M 10.5,37.5 A 35,35 1 0 0 34.5,37.5", 0, 'W', 1.5f, true)}, 0};
    gVP[1][eng::KING] = {{VS(VP_K_CROSS, 0, 'B', 1.5f, true), VS(VP_K_TOP, 'B', 'B', 1.5f, false),
                          VS(VP_K_BODY, 'B', 'B', 1.5f, true),
                          VS("M 32,29.5 C 32,29.5 40.5,25.5 38.03,19.85 C 34.15,14 25,18 22.5,24.5 L 22.5,26.6 L 22.5,"
                             "24.5 C 20,18 10.85,14 6.97,19.85 C 4.5,25.5 13,29.5 13,29.5", 0, 'W', 1.5f, true),
                          VS(VP_K_BANDS, 0, 'W', 1.5f, true)}, 0};
}

// --- разбор пути SVG ---
static void arcPts(std::vector<VPt> &out, float x1, float y1, float rx, float ry, float phiDeg, int fa, int fs, float x2,
                   float y2) {
    if (rx == 0 || ry == 0) {
        out.push_back({x2, y2});
        return;
    }
    double phi = phiDeg * 3.14159265358979 / 180.0, c = std::cos(phi), s = std::sin(phi);
    double dx = (x1 - x2) / 2.0, dy = (y1 - y2) / 2.0;
    double xp = c * dx + s * dy, yp = -s * dx + c * dy;
    double Rx = std::fabs(rx), Ry = std::fabs(ry);
    double lam = xp * xp / (Rx * Rx) + yp * yp / (Ry * Ry);
    if (lam > 1) {
        Rx *= std::sqrt(lam);
        Ry *= std::sqrt(lam);
    }
    double num = Rx * Rx * Ry * Ry - Rx * Rx * yp * yp - Ry * Ry * xp * xp;
    double den = Rx * Rx * yp * yp + Ry * Ry * xp * xp;
    double co = den > 0 ? std::sqrt(std::max(0.0, num / den)) : 0;
    if (fa == fs) co = -co;
    double cxp = co * Rx * yp / Ry, cyp = -co * Ry * xp / Rx;
    double cx = c * cxp - s * cyp + (x1 + x2) / 2.0, cy = s * cxp + c * cyp + (y1 + y2) / 2.0;
    auto ang = [](double ux, double uy, double vx, double vy) {
        double a = std::atan2(ux * vy - uy * vx, ux * vx + uy * vy);
        return a;
    };
    double th1 = ang(1, 0, (xp - cxp) / Rx, (yp - cyp) / Ry);
    double dth = ang((xp - cxp) / Rx, (yp - cyp) / Ry, (-xp - cxp) / Rx, (-yp - cyp) / Ry);
    if (!fs && dth > 0) dth -= 2 * 3.14159265358979;
    else if (fs && dth < 0) dth += 2 * 3.14159265358979;
    int n = 28;
    for (int i = 1; i <= n; i++) {
        double t = th1 + dth * i / n;
        out.push_back({(float)(cx + Rx * std::cos(t) * c - Ry * std::sin(t) * s),
                       (float)(cy + Rx * std::cos(t) * s + Ry * std::sin(t) * c)});
    }
}

static void parsePath(const char *d, std::vector<VSub> &out) {
    const char *p = d;
    char cmd = 0;
    float cx = 0, cy = 0, sx = 0, sy = 0, lcx = 0, lcy = 0;
    bool haveSub = false;
    auto skip = [&]() {
        while (*p == ' ' || *p == ',' || *p == '\n' || *p == '\t') p++;
    };
    auto num = [&](float &v) -> bool {
        skip();
        if (!*p || ((*p < '0' || *p > '9') && *p != '-' && *p != '+' && *p != '.')) return false;
        char *e = nullptr;
        v = strtof(p, &e);
        if (e == p) return false;
        p = e;
        return true;
    };
    auto cur = [&]() -> VSub & {
        if (!haveSub) {
            VSub s;
            s.closed = false;
            s.p.push_back({cx, cy});
            out.push_back(s);
            haveSub = true;
        }
        return out.back();
    };
    for (;;) {
        skip();
        if (!*p) break;
        if ((*p >= 'A' && *p <= 'Z') || (*p >= 'a' && *p <= 'z')) cmd = *p++;
        else if (!cmd) break;
        bool rel = cmd >= 'a';
        char C = (char)(rel ? cmd - 32 : cmd);
        float ox = rel ? cx : 0, oy = rel ? cy : 0;
        if (C == 'Z') {
            if (haveSub) out.back().closed = true;
            cx = sx;
            cy = sy;
            haveSub = false;
            lcx = cx;
            lcy = cy;
            cmd = 0;
            continue;
        }
        if (C == 'M') {
            float x, y;
            if (!num(x) || !num(y)) break;
            cx = ox + x;
            cy = oy + y;
            sx = cx;
            sy = cy;
            haveSub = false;
            cur();
            lcx = cx;
            lcy = cy;
            cmd = rel ? 'l' : 'L';
        } else if (C == 'L') {
            float x, y;
            if (!num(x) || !num(y)) break;
            VSub &s = cur();
            cx = ox + x;
            cy = oy + y;
            s.p.push_back({cx, cy});
            lcx = cx;
            lcy = cy;
        } else if (C == 'H' || C == 'V') {
            float v;
            if (!num(v)) break;
            VSub &s = cur();
            if (C == 'H') cx = (rel ? cx : 0) + v;
            else cy = (rel ? cy : 0) + v;
            s.p.push_back({cx, cy});
            lcx = cx;
            lcy = cy;
        } else if (C == 'C' || C == 'S') {
            float x1, y1, x2, y2, x, y;
            if (C == 'C') {
                if (!num(x1) || !num(y1)) break;
                x1 += ox;
                y1 += oy;
            } else {
                x1 = 2 * cx - lcx;
                y1 = 2 * cy - lcy;
            }
            if (!num(x2) || !num(y2) || !num(x) || !num(y)) break;
            x2 += ox; y2 += oy; x += ox; y += oy;
            VSub &s = cur();
            int n = 20;
            for (int i = 1; i <= n; i++) {
                float t = (float)i / n, u = 1 - t;
                float a = u * u * u, b = 3 * u * u * t, c2 = 3 * u * t * t, e = t * t * t;
                s.p.push_back({a * cx + b * x1 + c2 * x2 + e * x, a * cy + b * y1 + c2 * y2 + e * y});
            }
            lcx = x2;
            lcy = y2;
            cx = x;
            cy = y;
        } else if (C == 'A') {
            float rx, ry, rot, fa, fs, x, y;
            if (!num(rx) || !num(ry) || !num(rot) || !num(fa) || !num(fs) || !num(x) || !num(y)) break;
            VSub &s = cur();
            arcPts(s.p, cx, cy, rx, ry, rot, fa != 0, fs != 0, ox + x, oy + y);
            cx = ox + x;
            cy = oy + y;
            lcx = cx;
            lcy = cy;
        } else {
            break;  // другие команды в наших контурах не встречаются
        }
    }
}

// --- растеризация в RGBA-буфер с суперсэмплингом ---
struct VRaster {
    int W, H;
    std::vector<uint32_t> px;  // 0 — прозрачно, иначе 0xFF000000 | rgb
};

static void vFillPolys(VRaster &r, const std::vector<std::vector<VPt>> &polys, uint32_t col) {
    struct E {
        float x0, y0, x1, y1;
        int dir;
    };
    std::vector<E> es;
    float ymin = 1e9f, ymax = -1e9f;
    for (auto &pl : polys) {
        size_t n = pl.size();
        if (n < 2) continue;
        for (size_t i = 0; i < n; i++) {
            VPt a = pl[i], b = pl[(i + 1) % n];
            if (a.y == b.y) continue;
            E e;
            if (a.y < b.y) { e.x0 = a.x; e.y0 = a.y; e.x1 = b.x; e.y1 = b.y; e.dir = 1; }
            else { e.x0 = b.x; e.y0 = b.y; e.x1 = a.x; e.y1 = a.y; e.dir = -1; }
            es.push_back(e);
            ymin = std::min(ymin, e.y0);
            ymax = std::max(ymax, e.y1);
        }
    }
    if (es.empty()) return;
    int y0 = std::max(0, (int)std::floor(ymin)), y1 = std::min(r.H - 1, (int)std::ceil(ymax));
    std::vector<std::pair<float, int>> xs;
    for (int y = y0; y <= y1; y++) {
        float sy = y + 0.5f;
        xs.clear();
        for (auto &e : es)
            if (sy >= e.y0 && sy < e.y1) xs.push_back({e.x0 + (sy - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0), e.dir});
        if (xs.size() < 2) continue;
        std::sort(xs.begin(), xs.end());
        int w = 0;
        for (size_t i = 0; i + 1 < xs.size(); i++) {
            w += xs[i].second;
            if (w == 0) continue;
            int a = std::max(0, (int)std::ceil(xs[i].first - 0.5f));
            int b = std::min(r.W - 1, (int)std::ceil(xs[i + 1].first - 0.5f) - 1);
            uint32_t *row = &r.px[(size_t)y * r.W];
            for (int x = a; x <= b; x++) row[x] = col;
        }
    }
}

static void vDisc(VRaster &r, float cx, float cy, float rad, uint32_t col) {
    int x0 = std::max(0, (int)(cx - rad - 1)), x1 = std::min(r.W - 1, (int)(cx + rad + 1));
    int y0 = std::max(0, (int)(cy - rad - 1)), y1 = std::min(r.H - 1, (int)(cy + rad + 1));
    float r2 = rad * rad;
    for (int y = y0; y <= y1; y++)
        for (int x = x0; x <= x1; x++) {
            float dx = x + 0.5f - cx, dy = y + 0.5f - cy;
            if (dx * dx + dy * dy <= r2) r.px[(size_t)y * r.W + x] = col;
        }
}

static void vStroke(VRaster &r, const std::vector<VPt> &pl, bool closed, float w, bool roundCap, uint32_t col) {
    size_t n = pl.size();
    if (n < 2) return;
    float hw = w * 0.5f;
    size_t segs = closed ? n : n - 1;
    std::vector<std::vector<VPt>> one(1);
    for (size_t i = 0; i < segs; i++) {
        VPt a = pl[i], b = pl[(i + 1) % n];
        float dx = b.x - a.x, dy = b.y - a.y, L = std::sqrt(dx * dx + dy * dy);
        if (L < 1e-4f) continue;
        float nx = -dy / L * hw, ny = dx / L * hw;
        one[0] = {{a.x + nx, a.y + ny}, {b.x + nx, b.y + ny}, {b.x - nx, b.y - ny}, {a.x - nx, a.y - ny}};
        vFillPolys(r, one, col);
    }
    // соединения (скруглённые) и концы
    for (size_t i = 0; i < n; i++) {
        bool end = !closed && (i == 0 || i == n - 1);
        if (end && !roundCap) continue;
        vDisc(r, pl[i].x, pl[i].y, hw, col);
    }
}

static uint32_t vCol(char c) {
    switch (c) {
        case 'W': return 0xFFFFFFFFu;
        case 'L': return 0xFFECECECu;
        default: return 0xFF000000u;
    }
}

// Рисует фигуру в RGBA-байты (size x size), со сглаживанием
static void vRenderPiece(int color, int type, int size, std::vector<uint8_t> &rgba) {
    const int SS = 3;
    VRaster r;
    r.W = r.H = size * SS;
    r.px.assign((size_t)r.W * r.H, 0);
    const VPiece &vp = gVP[color][type];
    float sc = (float)r.W / 45.0f;
    for (auto &sh : vp.shapes) {
        std::vector<VSub> subs;
        parsePath(sh.d, subs);
        std::vector<std::vector<VPt>> polys;
        for (auto &s : subs) {
            std::vector<VPt> q;
            for (auto v : s.p) {
                float x = v.x, y = v.y;
                if (sh.useM) {
                    float nx = sh.m[0] * x + sh.m[2] * y + sh.m[4];
                    float ny = sh.m[1] * x + sh.m[3] * y + sh.m[5];
                    x = nx;
                    y = ny;
                }
                q.push_back({x * sc, (y + vp.dy) * sc});
            }
            polys.push_back(q);
        }
        if (sh.fill) vFillPolys(r, polys, vCol(sh.fill));
        if (sh.stroke)
            for (size_t i = 0; i < polys.size(); i++) vStroke(r, polys[i], subs[i].closed, sh.sw * sc, sh.roundCap, vCol(sh.stroke));
    }
    rgba.assign((size_t)size * size * 4, 0);
    for (int y = 0; y < size; y++)
        for (int x = 0; x < size; x++) {
            int cnt = 0, sr = 0, sg = 0, sb = 0;
            for (int j = 0; j < SS; j++)
                for (int i = 0; i < SS; i++) {
                    uint32_t v = r.px[(size_t)(y * SS + j) * r.W + x * SS + i];
                    if (v) {
                        cnt++;
                        sr += (v >> 16) & 255;
                        sg += (v >> 8) & 255;
                        sb += v & 255;
                    }
                }
            uint8_t *o = &rgba[((size_t)y * size + x) * 4];
            if (cnt) {
                o[0] = (uint8_t)(sr / cnt);
                o[1] = (uint8_t)(sg / cnt);
                o[2] = (uint8_t)(sb / cnt);
                o[3] = (uint8_t)(cnt * 255 / (SS * SS));
            }
        }
}

static SDL_Texture *gPieceTex[2][7];
static int gPieceTexSize = 0;
static bool gTexDirty = true;
static bool gUseTex = true;

static void freePieceTex() {
    for (int c = 0; c < 2; c++)
        for (int t = 0; t < 7; t++) {
            if (gPieceTex[c][t]) SDL_DestroyTexture(gPieceTex[c][t]);
            gPieceTex[c][t] = nullptr;
        }
    gPieceTexSize = 0;
}

static void buildPieceTex(int cell) {
    freePieceTex();
    gTexDirty = false;
    if (!gUseTex) return;
    int ts = std::max(48, std::min(360, cell * 2));
    std::vector<uint8_t> rgba;
    for (int c = 0; c < 2; c++)
        for (int t = 1; t <= 6; t++) {
            vRenderPiece(c, t, ts, rgba);
            SDL_Texture *tx = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STATIC, ts, ts);
            if (!tx) {
                gUseTex = false;
                freePieceTex();
                return;
            }
            SDL_UpdateTexture(tx, nullptr, rgba.data(), ts * 4);
            SDL_SetTextureBlendMode(tx, SDL_BLENDMODE_BLEND);
            SDL_SetTextureScaleMode(tx, SDL_ScaleModeLinear);
            gPieceTex[c][t] = tx;
        }
    gPieceTexSize = cell;
}

static void ensurePieceTex(int cell) {
    if (gTexDirty || (gUseTex && gPieceTexSize != cell)) buildPieceTex(cell);
}

static void drawPiece(int piece, float x, float y, float s, int alpha = 255) {
    if (!piece) return;
    int c = eng::pColor(piece), t = eng::pType(piece);
    if (gUseTex && gPieceTex[c][t]) {
        SDL_FRect d;
        d.x = x; d.y = y; d.w = s; d.h = s;
        SDL_SetTextureAlphaMod(gPieceTex[c][t], (Uint8)alpha);
        SDL_RenderCopyF(R, gPieceTex[c][t], nullptr, &d);
    } else {
        drawPieceShape(c, t, x, y, s, true);
    }
}

// =====================================================================
//                             ЗВУК
// =====================================================================
struct Voice {
    float freq, t, dur, vol;
    int kind;  // 0 — тон, 1 — щелчок
    bool on;
};
static Voice gVoices[8];
static bool gAudioOk = false;
static uint32_t gNoise = 22222;
static const int AUDIO_RATE = 22050;

static void SDLCALL audioCb(void *, Uint8 *stream, int len) {
    Sint16 *out = (Sint16 *)stream;
    int n = len / 2;
    for (int i = 0; i < n; i++) {
        float s = 0;
        for (auto &v : gVoices) {
            if (!v.on) continue;
            float env;
            float att = 0.004f;
            if (v.t < att) env = v.t / att;
            else env = std::exp(-(v.t - att) * (v.kind == 1 ? 55.0f : 9.0f / v.dur));
            float x;
            if (v.kind == 1) {
                gNoise = gNoise * 1664525u + 1013904223u;
                float nz = ((gNoise >> 9) & 0xFFFF) / 32768.0f - 1.0f;
                x = nz * 0.55f + std::sin(6.2831853f * v.freq * v.t) * 0.6f;
            } else {
                x = std::sin(6.2831853f * v.freq * v.t) + 0.25f * std::sin(6.2831853f * v.freq * 2 * v.t);
            }
            s += x * env * v.vol;
            v.t += 1.0f / AUDIO_RATE;
            if (v.t >= v.dur) v.on = false;
        }
        if (s > 1) s = 1;
        if (s < -1) s = -1;
        out[i] = (Sint16)(s * 30000);
    }
}

static void audioInit() {
    for (auto &v : gVoices) v.on = false;
    if (SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) return;
    SDL_AudioSpec want;
    SDL_zero(want);
    want.freq = AUDIO_RATE;
    want.format = AUDIO_S16SYS;
    want.channels = 1;
    want.samples = 512;
    want.callback = audioCb;
    if (SDL_OpenAudio(&want, nullptr) != 0) return;
    gAudioOk = true;
    SDL_PauseAudio(0);
}

static void addVoice(float f, float dur, float vol, int kind, float delay = 0) {
    for (auto &v : gVoices)
        if (!v.on) {
            v.freq = f;
            v.dur = dur + delay;
            v.t = -delay;
            v.vol = vol;
            v.kind = kind;
            v.on = true;
            return;
        }
}

enum { SND_MOVE, SND_CAPTURE, SND_CHECK, SND_END, SND_CLICK };
static int gSoundOn = 1;
static void playSound(int k) {
    if (!gAudioOk || !gSoundOn) return;
    SDL_LockAudio();
    switch (k) {
        case SND_MOVE: addVoice(180, 0.09f, 0.55f, 1); break;
        case SND_CAPTURE:
            addVoice(150, 0.11f, 0.6f, 1);
            addVoice(320, 0.10f, 0.35f, 1, 0.045f);
            break;
        case SND_CHECK:
            addVoice(180, 0.09f, 0.5f, 1);
            addVoice(880, 0.25f, 0.22f, 0, 0.03f);
            break;
        case SND_END:
            addVoice(523, 0.6f, 0.2f, 0);
            addVoice(659, 0.6f, 0.18f, 0, 0.12f);
            addVoice(784, 0.8f, 0.18f, 0, 0.24f);
            break;
        case SND_CLICK: addVoice(900, 0.04f, 0.15f, 0); break;
    }
    SDL_UnlockAudio();
}

// =====================================================================
//                        СОСТОЯНИЕ ИГРЫ
// =====================================================================
enum { SC_MENU, SC_SETUP, SC_GAME, SC_STATS, SC_LEARN, SC_LESSON, SC_NET, SC_REVIEW, SC_EDITOR };
enum { OV_NONE, OV_PROMO, OV_CONFIRM, OV_RESULT, OV_CHOOSE };
enum { CF_NONE, CF_RESIGN, CF_NEW, CF_RESET, CF_NET_DRAW, CF_NET_NEW, CF_NET_LEAVE, CF_NET_LOST };
enum { MODE_BOT = 0, MODE_TWO = 1, MODE_NET = 2 };

struct Settings {
    int level = 2;
    int color = 0;  // 0 белые, 1 чёрные, 2 случайно
    int clock = 0;  // 0 нет, 1 = 5 мин, 2 = 10, 3 = 15
};
struct Stats {
    int wins = 0, losses = 0, draws = 0, two = 0;
    int netW = 0, netL = 0, netD = 0;
};
struct Match {
    bool active = false;
    int mode = MODE_BOT;
    int human = eng::WHITE;
    int level = 2;
    int clockInit = 0;  // мс, 0 — без часов
    long long tLeft[2] = {0, 0};
    bool flip = false;
    bool recorded = false;
    Game g;
};

static Settings gSet;
static Stats gStats;
static Match gM;
static int gScreen = SC_MENU;
static int gOverlay = OV_NONE;
static int gConfirm = CF_NONE;
static int gSetupMode = MODE_BOT;
static bool gRunning = true;
static bool gPaused = false;
static Uint32 gLastTick = 0;
static SDL_mutex *gLock = nullptr;
static std::string gSavePath;
static int gViewSide = eng::WHITE;

static int gSel = -1;
static std::vector<eng::Move> gTargets;
static bool gWasSelected = false;
struct Drag {
    bool active = false, started = false;
    int sq = -1;
} gDrag;
static int gPromoFrom = -1, gPromoTo = -1;
struct Anim {
    int piece, from, to;
};
static std::vector<Anim> gAnims;
static Uint32 gAnimStart = 0;
static const Uint32 ANIM_MS = 170;
static bool gResultPending = false;
static Uint32 gResultAt = 0;
static int gListScroll = 0;
static int gViewPly = -1;       // просмотр истории: позиция после N ходов (-1 — текущая)
static bool gListFollow = false; // прокрутить список к выбранному ходу
static int gSolved[16] = {0};  // решённые задачи по темам (биты = страницы)

struct Pointer {
    bool down = false;
    bool finger = false;
    SDL_FingerID fid = 0;
    float x = 0, y = 0, sx = 0, sy = 0;
    bool listDrag = false;
    int listStart = 0;
    bool outside = false;
} gPtr;

// ------------------------- сеть: соединение -------------------------
// Игра по локальной сети (один Wi-Fi или точка доступа): один телефон создаёт
// игру (TCP-сервер + рассылка о себе по UDP), второй находит её или вводит адрес.
enum { NS_IDLE, NS_HOSTING, NS_CONNECTING, NS_CONNECTED };
static const int NET_TCP_PORT = 47474, NET_UDP_PORT = 47475;
struct NetState {
    int state = NS_IDLE;
    bool isHost = false;
    sock_t lsock = SOCK_BAD, sock = SOCK_BAD, udp = SOCK_BAD, scan = SOCK_BAD;
    std::string in, out;
    Uint32 lastRecv = 0, lastSend = 0, lastBcast = 0, connStart = 0;
    std::string myIp, peerIp;
    bool lost = false;
};
static NetState gNet;
struct FoundGame {
    std::string ip;
    int color, clockMin;
    Uint32 seen;
};
static std::vector<FoundGame> gFound;
static Match gBackup;  // офлайн-партия, отложенная на время сетевой игры
static bool gHaveBackup = false;
static std::string gNetLastIp;
static std::string gToast;
static Uint32 gToastUntil = 0;
static void toast(const std::string &s) {
    gToast = s;
    gToastUntil = SDL_GetTicks() + 2800;
}

static bool netStartup() {
#if defined(_WIN32)
    static bool ok = false;
    if (!ok) {
        WSADATA w;
        ok = WSAStartup(MAKEWORD(2, 2), &w) == 0;
    }
    return ok;
#else
    return true;
#endif
}
static void closeSock(sock_t &s) {
    if (s != SOCK_BAD) {
        sockClose(s);
        s = SOCK_BAD;
    }
}
static void netNoDelay(sock_t s) {
    int one = 1;
    setsockopt(s, IPPROTO_TCP, TCP_NODELAY, (const char *)&one, sizeof one);
}

static void netFlush() {
    if (gNet.sock == SOCK_BAD || gNet.state != NS_CONNECTED) return;
    while (!gNet.out.empty()) {
        int n = (int)send(gNet.sock, gNet.out.data(), (int)gNet.out.size(), MSG_NOSIGNAL);
        if (n > 0) {
            gNet.out.erase(0, (size_t)n);
            gNet.lastSend = SDL_GetTicks();
        } else {
            if (n < 0 && !sockWouldBlock()) gNet.lost = true;
            break;
        }
    }
}
static bool netConnected() { return gNet.state == NS_CONNECTED && !gNet.lost; }
static void netSendLine(const std::string &l) {
    if (gNet.state != NS_CONNECTED) return;
    gNet.out += l;
    gNet.out += "\n";
    netFlush();
}
static void netCloseAll() {
    closeSock(gNet.lsock);
    closeSock(gNet.sock);
    closeSock(gNet.udp);
    closeSock(gNet.scan);
    gNet.state = NS_IDLE;
    gNet.in.clear();
    gNet.out.clear();
    gNet.lost = false;
    gFound.clear();
}

// Свой адрес в сети: «подключаем» UDP-сокет к внешнему адресу (пакеты не уходят)
static std::string netLocalIp() {
    if (!netStartup()) return "";
    const char *probes[] = {"8.8.8.8", "192.168.1.1", "192.168.0.1", "192.168.43.1", "10.0.0.1", "172.16.0.1"};
    for (const char *pr : probes) {
        sock_t s = socket(AF_INET, SOCK_DGRAM, 0);
        if (s == SOCK_BAD) continue;
        sockaddr_in a;
        memset(&a, 0, sizeof a);
        a.sin_family = AF_INET;
        a.sin_port = htons(53);
        inet_pton(AF_INET, pr, &a.sin_addr);
        std::string r;
        if (connect(s, (sockaddr *)&a, sizeof a) == 0) {
            sockaddr_in me;
            memset(&me, 0, sizeof me);
            socklen_t len = sizeof me;
            if (getsockname(s, (sockaddr *)&me, &len) == 0) {
                char buf[64] = {0};
                inet_ntop(AF_INET, &me.sin_addr, buf, sizeof buf);
                r = buf;
            }
        }
        sockClose(s);
        if (!r.empty() && r != "0.0.0.0" && r.compare(0, 4, "127.") != 0) return r;
    }
    return "";
}

static bool netHost() {
    netCloseAll();
    if (!netStartup()) return false;
    sock_t s = socket(AF_INET, SOCK_STREAM, 0);
    if (s == SOCK_BAD) return false;
    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, sizeof one);
    sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    a.sin_port = htons(NET_TCP_PORT);
    if (bind(s, (sockaddr *)&a, sizeof a) != 0 || listen(s, 2) != 0) {
        sockClose(s);
        return false;
    }
    sockNonBlock(s);
    gNet.lsock = s;
    sock_t u = socket(AF_INET, SOCK_DGRAM, 0);
    if (u != SOCK_BAD) {
        setsockopt(u, SOL_SOCKET, SO_BROADCAST, (const char *)&one, sizeof one);
        sockNonBlock(u);
        gNet.udp = u;
    }
    gNet.state = NS_HOSTING;
    gNet.isHost = true;
    gNet.myIp = netLocalIp();
    gNet.lastBcast = 0;
    return true;
}

static void netScanStart() {
    closeSock(gNet.scan);
    gFound.clear();
    if (!netStartup()) return;
    sock_t u = socket(AF_INET, SOCK_DGRAM, 0);
    if (u == SOCK_BAD) return;
    int one = 1;
    setsockopt(u, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, sizeof one);
    setsockopt(u, SOL_SOCKET, SO_BROADCAST, (const char *)&one, sizeof one);
    sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    a.sin_port = htons(NET_UDP_PORT);
    if (bind(u, (sockaddr *)&a, sizeof a) != 0) {
        sockClose(u);
        return;
    }
    sockNonBlock(u);
    gNet.scan = u;
}

static bool validIp(const std::string &ip) {
    in_addr a;
    return inet_pton(AF_INET, ip.c_str(), &a) == 1;
}

static bool netConnect(const std::string &ip) {
    netCloseAll();
    if (!netStartup() || !validIp(ip)) return false;
    sock_t s = socket(AF_INET, SOCK_STREAM, 0);
    if (s == SOCK_BAD) return false;
    sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons(NET_TCP_PORT);
    inet_pton(AF_INET, ip.c_str(), &a.sin_addr);
    sockNonBlock(s);
    int r = connect(s, (sockaddr *)&a, sizeof a);
    if (r != 0 && !sockWouldBlock()) {
        sockClose(s);
        return false;
    }
    gNet.sock = s;
    gNet.state = NS_CONNECTING;
    gNet.connStart = SDL_GetTicks();
    gNet.peerIp = ip;
    gNet.isHost = false;
    return true;
}

static void netHandleLine(const std::string &l);  // протокол — ниже

static void netPollIO() {
    Uint32 now = SDL_GetTicks();
    // поиск игр: слушаем рассылку
    if (gNet.scan != SOCK_BAD) {
        char buf[256];
        for (;;) {
            sockaddr_in from;
            memset(&from, 0, sizeof from);
            socklen_t fl = sizeof from;
            int n = (int)recvfrom(gNet.scan, buf, sizeof buf - 1, 0, (sockaddr *)&from, &fl);
            if (n <= 0) break;
            buf[n] = 0;
            int port = 0, col = 0, clk = 0;
            if (sscanf(buf, "SHAHMATY_HOST %d %d %d", &port, &col, &clk) == 3 && port == NET_TCP_PORT) {
                char ip[64] = {0};
                inet_ntop(AF_INET, &from.sin_addr, ip, sizeof ip);
                bool found = false;
                for (auto &f : gFound)
                    if (f.ip == ip) { f.seen = now; f.color = col; f.clockMin = clk; found = true; }
                if (!found && gFound.size() < 6) {
                    FoundGame g;
                    g.ip = ip; g.color = col; g.clockMin = clk; g.seen = now;
                    gFound.push_back(g);
                }
            }
        }
        for (size_t i = 0; i < gFound.size();)
            if (now - gFound[i].seen > 4500) gFound.erase(gFound.begin() + (long)i);
            else i++;
    }
    if (gNet.state == NS_HOSTING) {
        if (gNet.udp != SOCK_BAD && now - gNet.lastBcast > 1000) {
            gNet.lastBcast = now;
            static const int MIN[4] = {0, 5, 10, 15};
            char msg[96];
            snprintf(msg, sizeof msg, "SHAHMATY_HOST %d %d %d", NET_TCP_PORT, gSet.color, MIN[gSet.clock]);
            sockaddr_in a;
            memset(&a, 0, sizeof a);
            a.sin_family = AF_INET;
            a.sin_port = htons(NET_UDP_PORT);
            a.sin_addr.s_addr = htonl(INADDR_BROADCAST);
            sendto(gNet.udp, msg, (int)strlen(msg), 0, (sockaddr *)&a, sizeof a);
            if (gNet.myIp.empty()) gNet.myIp = netLocalIp();
            size_t dot = gNet.myIp.rfind('.');
            if (dot != std::string::npos) {
                std::string bc = gNet.myIp.substr(0, dot) + ".255";
                if (inet_pton(AF_INET, bc.c_str(), &a.sin_addr) == 1)
                    sendto(gNet.udp, msg, (int)strlen(msg), 0, (sockaddr *)&a, sizeof a);
            }
        }
        sockaddr_in pa;
        memset(&pa, 0, sizeof pa);
        socklen_t pl = sizeof pa;
        sock_t c = accept(gNet.lsock, (sockaddr *)&pa, &pl);
        if (c != SOCK_BAD) {
            sockNonBlock(c);
            netNoDelay(c);
            char ip[64] = {0};
            inet_ntop(AF_INET, &pa.sin_addr, ip, sizeof ip);
            gNet.peerIp = ip;
            gNet.sock = c;
            closeSock(gNet.lsock);
            closeSock(gNet.udp);
            gNet.state = NS_CONNECTED;
            gNet.lastRecv = gNet.lastSend = now;
        }
    }
    if (gNet.state == NS_CONNECTING) {
        fd_set w;
        FD_ZERO(&w);
        FD_SET(gNet.sock, &w);
        timeval tv;
        tv.tv_sec = 0;
        tv.tv_usec = 0;
        int r = select((int)gNet.sock + 1, nullptr, &w, nullptr, &tv);
        bool fail = false;
        if (r > 0) {
            int err = 0;
            socklen_t el = sizeof err;
            getsockopt(gNet.sock, SOL_SOCKET, SO_ERROR, (char *)&err, &el);
            if (err == 0) {
                gNet.state = NS_CONNECTED;
                gNet.lastRecv = gNet.lastSend = now;
                netNoDelay(gNet.sock);
                netSendLine("HELLO SHAHMATY 1");
            } else {
                fail = true;
            }
        } else if (r < 0 || now - gNet.connStart > 6000) {
            fail = true;
        }
        if (fail) netCloseAll();
    }
    if (gNet.state == NS_CONNECTED && !gNet.lost) {
        netFlush();
        char buf[2048];
        for (;;) {
            int n = (int)recv(gNet.sock, buf, sizeof buf, 0);
            if (n > 0) {
                gNet.in.append(buf, (size_t)n);
                gNet.lastRecv = now;
                if (gNet.in.size() > 65536) { gNet.lost = true; break; }
            } else if (n == 0) {
                gNet.lost = true;
                break;
            } else {
                if (!sockWouldBlock()) gNet.lost = true;
                break;
            }
        }
        size_t p;
        while (gNet.state == NS_CONNECTED && (p = gNet.in.find('\n')) != std::string::npos) {
            std::string line = gNet.in.substr(0, p);
            gNet.in.erase(0, p + 1);
            if (!line.empty() && line.back() == '\r') line.pop_back();
            netHandleLine(line);
        }
        if (gNet.state == NS_CONNECTED) {
            if (now - gNet.lastSend > 2000) netSendLine("PING");
            if (now - gNet.lastRecv > 45000) gNet.lost = true;
        }
    }
}

// ------------------------- сохранение -------------------------
static void initSavePath() {
#if defined(__ANDROID__)
    const char *p = SDL_AndroidGetInternalStoragePath();
    if (p) gSavePath = std::string(p) + "/shahmaty.sav";
#endif
    if (gSavePath.empty()) {
        char *b = SDL_GetBasePath();
        if (b) {
            gSavePath = std::string(b) + "shahmaty.sav";
            SDL_free(b);
        } else {
            gSavePath = "shahmaty.sav";
        }
    }
}

static void saveAll() {
    std::string s;
    char buf[256];
    s += "SHAHMATY 1\n";
    // во время сетевой игры сохраняем отложенную офлайн-партию
    const Match &mm = gM.mode == MODE_NET ? gBackup : gM;
    snprintf(buf, sizeof buf, "STATS %d %d %d %d %d %d %d\n", gStats.wins, gStats.losses, gStats.draws, gStats.two,
             gStats.netW, gStats.netL, gStats.netD);
    s += buf;
    snprintf(buf, sizeof buf, "SET %d %d %d %d\n", gSet.level, gSet.color, gSet.clock, gSoundOn);
    s += buf;
    s += "LEARN";
    for (int i = 0; i < 16; i++) s += " " + std::to_string(gSolved[i]);
    s += "\n";
    if (!gNetLastIp.empty() && validIp(gNetLastIp)) s += "NETIP " + gNetLastIp + "\n";
    snprintf(buf, sizeof buf, "MATCH %d %d %d %d %d %lld %lld %d %d %d %d %d\n", mm.active ? 1 : 0, mm.mode, mm.human,
             mm.level, mm.clockInit, mm.tLeft[0], mm.tLeft[1], mm.flip ? 1 : 0, mm.recorded ? 1 : 0, mm.g.result,
             mm.g.reason, mm.g.loser);
    s += buf;
    if (!mm.g.startFen.empty()) s += "FEN " + mm.g.startFen + "\n";
    s += "MOVES";
    for (auto m : mm.g.moves) s += " " + eng::toUCI(m);
    s += "\nEND\n";
    std::string tmp = gSavePath + ".tmp";
    FILE *f = fopen(tmp.c_str(), "wb");
    if (!f) return;
    bool ok = fwrite(s.data(), 1, s.size(), f) == s.size();
    if (fflush(f) != 0) ok = false;
#ifdef SHAH_HAVE_FSYNC
    if (ok && fsync(fileno(f)) != 0) ok = false;
#endif
    if (fclose(f) != 0) ok = false;
    if (!ok) {
        remove(tmp.c_str());
        return;
    }
    if (rename(tmp.c_str(), gSavePath.c_str()) != 0) {
        remove(gSavePath.c_str());
        if (rename(tmp.c_str(), gSavePath.c_str()) != 0) remove(tmp.c_str());
    }
}

static void loadAll() {
    FILE *f = fopen(gSavePath.c_str(), "rb");
    if (!f) return;
    std::string data;
    char buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof buf, f)) > 0) data.append(buf, n);
    fclose(f);
    if (data.compare(0, 10, "SHAHMATY 1") != 0) return;
    if (data.find("\nEND") == std::string::npos) return;  // файл недописан
    size_t pos = 0;
    std::string movesLine, startFen;
    int mActive = 0, mMode = 0, mHuman = 0, mLevel = 2, mClock = 0, mFlip = 0, mRec = 0, mRes = 0, mReason = 0,
        mLoser = -1;
    long long t0 = 0, t1 = 0;
    bool haveMatch = false;
    while (pos < data.size()) {
        size_t e = data.find('\n', pos);
        if (e == std::string::npos) e = data.size();
        std::string line = data.substr(pos, e - pos);
        pos = e + 1;
        if (line.compare(0, 6, "STATS ") == 0) {
            Stats st;
            if (sscanf(line.c_str() + 6, "%d %d %d %d %d %d %d", &st.wins, &st.losses, &st.draws, &st.two, &st.netW,
                       &st.netL, &st.netD) >= 4)
                gStats = st;
        } else if (line.compare(0, 6, "NETIP ") == 0) {
            if (validIp(line.substr(6))) gNetLastIp = line.substr(6);
        } else if (line.compare(0, 4, "SET ") == 0) {
            int a, b, c, d;
            if (sscanf(line.c_str() + 4, "%d %d %d %d", &a, &b, &c, &d) == 4) {
                gSet.level = std::max(1, std::min(5, a));
                gSet.color = std::max(0, std::min(2, b));
                gSet.clock = std::max(0, std::min(3, c));
                gSoundOn = d ? 1 : 0;
            }
        } else if (line.compare(0, 6, "MATCH ") == 0) {
            if (sscanf(line.c_str() + 6, "%d %d %d %d %d %lld %lld %d %d %d %d %d", &mActive, &mMode, &mHuman, &mLevel,
                       &mClock, &t0, &t1, &mFlip, &mRec, &mRes, &mReason, &mLoser) >= 11)
                haveMatch = true;
        } else if (line.compare(0, 6, "LEARN ") == 0) {
            const char *q = line.c_str() + 6;
            for (int k = 0; k < 16 && *q; k++) {
                char *end = nullptr;
                long v = strtol(q, &end, 10);
                if (end == q) break;
                gSolved[k] = (int)v;
                q = end;
            }
        } else if (line.compare(0, 5, "MOVES") == 0) {
            movesLine = line.substr(5);
        } else if (line.compare(0, 4, "FEN ") == 0) {
            startFen = line.substr(4);
        }
    }
    if (!haveMatch) return;
    gM.active = mActive != 0;
    gM.mode = mMode == MODE_TWO ? MODE_TWO : MODE_BOT;
    gM.human = mHuman ? eng::BLACK : eng::WHITE;
    gM.level = std::max(1, std::min(5, mLevel));
    gM.clockInit = std::max(0, mClock);
    gM.tLeft[0] = std::max(0LL, t0);
    gM.tLeft[1] = std::max(0LL, t1);
    gM.flip = mFlip != 0;
    gM.recorded = mRec != 0;
    gM.g.reset(startFen);
    size_t i = 0;
    while (i < movesLine.size()) {
        while (i < movesLine.size() && movesLine[i] == ' ') i++;
        size_t j = i;
        while (j < movesLine.size() && movesLine[j] != ' ') j++;
        if (j > i) {
            std::string u = movesLine.substr(i, j - i);
            eng::MoveList ml;
            gM.g.cur.genLegal(ml);
            bool found = false;
            for (int k = 0; k < ml.n; k++)
                if (eng::toUCI(ml.m[k]) == u) {
                    gM.g.play(ml.m[k]);
                    found = true;
                    break;
                }
            if (!found || gM.g.result != RES_NONE) break;
        }
        i = j;
    }
    if (mRes >= RES_WHITE && mRes <= RES_DRAW && gM.g.result == RES_NONE) {
        gM.g.result = mRes;
        gM.g.reason = mReason;
        gM.g.loser = mLoser;
    }
    if (gM.g.result != RES_NONE && !gM.recorded) gM.recorded = true;
    gViewSide = gM.g.cur.side;
}

// ------------------------- бот -------------------------
struct BotJob {
    eng::Board b;
    std::vector<uint64_t> hist;
    int level = 1;
    Uint32 timeMs = 1000;
    int gamePly = 0;
    uint32_t seed = 1;
    std::atomic<bool> stop{false};
    std::atomic<bool> done{false};
    eng::Move result = 0;
};
static BotJob *gJob = nullptr;
static SDL_Thread *gThread = nullptr;
static Uint32 gBotStart = 0;

static int SDLCALL botThreadFn(void *p) {
    BotJob *j = (BotJob *)p;
    j->result = eng::think(j->b, j->hist, j->level, j->timeMs, j->gamePly, j->seed, &j->stop);
    j->done = true;
    return 0;
}

static bool botThinking() { return gThread != nullptr; }

static void cancelBot() {
    if (!gThread) return;
    gJob->stop = true;
    SDL_WaitThread(gThread, nullptr);
    gThread = nullptr;
    delete gJob;
    gJob = nullptr;
}

static void startBot() {
    if (gThread || !gM.active || gM.mode != MODE_BOT || gM.g.result != RES_NONE) return;
    if (gM.g.cur.side == gM.human) return;
    static const Uint32 LIM[6] = {0, 500, 800, 1100, 1400, 2000};
    gJob = new BotJob();
    gJob->b = gM.g.cur;
    gJob->hist = gM.g.hashes;
    gJob->level = gM.level;
    Uint32 lim = LIM[gM.level];
    if (gM.clockInit > 0) {
        long long left = gM.tLeft[gM.g.cur.side];
        long long cap = left / 25 + 50;
        if (cap < (long long)lim) lim = (Uint32)std::max(60LL, cap);
    }
    gJob->timeMs = lim;
    gJob->gamePly = (int)gM.g.moves.size() + (gM.g.startFen.empty() ? 0 : 40);  // своя позиция — без «дебютной» случайности
    gJob->seed = (uint32_t)SDL_GetPerformanceCounter() ^ 0x9E3779B9u;
    gBotStart = SDL_GetTicks();
    gThread = SDL_CreateThreadWithStackSize(botThreadFn, "shahbot", 4 * 1024 * 1024, gJob);
    if (!gThread) {
        // Без потока считаем прямо здесь (очень редкий случай)
        botThreadFn(gJob);
        eng::Move m = gJob->result;
        delete gJob;
        gJob = nullptr;
        (void)m;
    }
}

// ------------------------- логика партии -------------------------
static void clearSel() {
    gSel = -1;
    gTargets.clear();
    gDrag.active = false;
    gDrag.started = false;
}

// ----- просмотр истории ходов -----
static bool viewing() { return gViewPly >= 0 && gViewPly < (int)gM.g.moves.size(); }
static const eng::Board &viewBoard() { return viewing() ? gM.g.before[(size_t)gViewPly] : gM.g.cur; }
static int viewPly() { return viewing() ? gViewPly : (int)gM.g.moves.size(); }
// ----- свои стрелки и кружки на доске (для обдумывания ходов) -----
struct UArrow {
    int a, b;
};
static std::vector<UArrow> gUArrows;
static std::vector<int> gUCircles;
static bool gArrowMode = false;   // режим «карандаш»: любое движение рисует стрелку
static bool gArrowDrag = false;   // сейчас тянем стрелку
static int gArrowFrom = -1;
static void clearUserMarks() {
    gUArrows.clear();
    gUCircles.clear();
    gArrowDrag = false;
}
static void toggleArrow(int a, int b) {
    for (size_t i = 0; i < gUArrows.size(); i++)
        if (gUArrows[i].a == a && gUArrows[i].b == b) {
            gUArrows.erase(gUArrows.begin() + (long)i);
            return;
        }
    UArrow u;
    u.a = a;
    u.b = b;
    gUArrows.push_back(u);
}
static void toggleCircle(int sq) {
    for (size_t i = 0; i < gUCircles.size(); i++)
        if (gUCircles[i] == sq) {
            gUCircles.erase(gUCircles.begin() + (long)i);
            return;
        }
    gUCircles.push_back(sq);
}

static void navTo(int ply) {
    clearUserMarks();
    int n = (int)gM.g.moves.size();
    if (ply < 0) ply = 0;
    gViewPly = ply >= n ? -1 : ply;
    clearSel();
    gAnims.clear();
    gListFollow = true;
}

static void computeTargets() {
    gTargets.clear();
    if (gSel < 0) return;
    eng::MoveList ml;
    gM.g.cur.genLegal(ml);
    for (int i = 0; i < ml.n; i++)
        if (eng::mFrom(ml.m[i]) == gSel) gTargets.push_back(ml.m[i]);
}

static bool isTarget(int s) {
    for (auto m : gTargets)
        if (eng::mTo(m) == s) return true;
    return false;
}

static void recordResult() {
    if (gM.recorded || gM.g.result == RES_NONE) return;
    gM.recorded = true;
    if (gM.mode == MODE_BOT) {
        if (gM.g.result == RES_DRAW) gStats.draws++;
        else if ((gM.g.result == RES_WHITE) == (gM.human == eng::WHITE)) gStats.wins++;
        else gStats.losses++;
    } else if (gM.mode == MODE_NET) {
        if (gM.g.result == RES_DRAW) gStats.netD++;
        else if ((gM.g.result == RES_WHITE) == (gM.human == eng::WHITE)) gStats.netW++;
        else gStats.netL++;
    } else {
        gStats.two++;
    }
}

static void onGameEnd() {
    cancelBot();
    clearSel();
    recordResult();
    gResultPending = true;
    gResultAt = SDL_GetTicks() + 650;
    playSound(SND_END);
    saveAll();
}

static void playMove(eng::Move m, bool animate) {
    eng::Board &b = gM.g.cur;
    int from = eng::mFrom(m), to = eng::mTo(m);
    bool cap = (eng::mFlags(m) & eng::F_CAP) != 0;
    bool castle = (eng::mFlags(m) & eng::F_CASTLE) != 0;
    int piece = b.sq[from];
    int mover = b.side;
    gM.g.play(m);
    if (gM.mode == MODE_NET && mover == gM.human)
        netSendLine("MOVE " + std::to_string(gM.g.moves.size() - 1) + " " + eng::toUCI(m) + " " +
                    std::to_string(gM.tLeft[mover]));
    gAnims.clear();
    if (animate) {
        Anim a;
        a.piece = gM.g.cur.sq[to];
        a.from = from;
        a.to = to;
        gAnims.push_back(a);
        if (castle) {
            Anim r;
            int rf = to > from ? to + 1 : to - 2, rt = to > from ? to - 1 : to + 1;
            r.piece = eng::mkPiece(eng::pColor(piece), eng::ROOK);
            r.from = rf;
            r.to = rt;
            gAnims.push_back(r);
        }
        gAnimStart = SDL_GetTicks();
    }
    clearSel();
    gListScroll = 0;
    gViewPly = -1;
    clearUserMarks();
    if (gM.g.cur.inCheck(gM.g.cur.side)) playSound(SND_CHECK);
    else playSound(cap ? SND_CAPTURE : SND_MOVE);
    if (gM.g.result != RES_NONE) {
        onGameEnd();
    } else {
        saveAll();
        startBot();
    }
}

static void tryMove(int from, int to, bool animate) {
    std::vector<eng::Move> c;
    for (auto m : gTargets)
        if (eng::mFrom(m) == from && eng::mTo(m) == to) c.push_back(m);
    if (c.empty()) return;
    if (c.size() > 1) {
        gPromoFrom = from;
        gPromoTo = to;
        gOverlay = OV_PROMO;
        gDrag.active = false;
        return;
    }
    playMove(c[0], animate);
}

static void cancelReview();
static void newMatch(int mode, int level, int colorChoice, int clockChoice, const std::string &fen = std::string()) {
    cancelBot();
    cancelReview();
    gM.active = true;
    gM.mode = mode;
    gM.level = level;
    if (colorChoice == 2) gM.human = (SDL_GetPerformanceCounter() >> 3) & 1 ? eng::BLACK : eng::WHITE;
    else gM.human = colorChoice == 1 ? eng::BLACK : eng::WHITE;
    static const int MIN[4] = {0, 5, 10, 15};
    gM.clockInit = MIN[clockChoice] * 60 * 1000;
    gM.tLeft[0] = gM.tLeft[1] = gM.clockInit;
    gM.flip = false;
    gM.recorded = false;
    gM.g.reset(fen);
    gViewSide = gM.g.cur.side;
    clearSel();
    gAnims.clear();
    gResultPending = false;
    gOverlay = OV_NONE;
    gListScroll = 0;
    gViewPly = -1;
    clearUserMarks();
    eng::ttClear();
    gScreen = SC_GAME;
    gLastTick = SDL_GetTicks();
    saveAll();
    startBot();
}

static void restartSame() {
    int clockChoice = 0;
    if (gM.clockInit == 5 * 60000) clockChoice = 1;
    else if (gM.clockInit == 10 * 60000) clockChoice = 2;
    else if (gM.clockInit == 15 * 60000) clockChoice = 3;
    int colorChoice = gM.human == eng::BLACK ? 1 : 0;
    if (gM.mode == MODE_BOT && gSet.color == 2) colorChoice = 2;
    newMatch(gM.mode, gM.level, colorChoice, clockChoice, gM.g.startFen);
}

static void doUndo() {
    if (!gM.active || gM.mode == MODE_NET) return;
    if (gM.mode == MODE_BOT) {
        if (gM.g.result != RES_NONE) return;
        if (botThinking()) {
            cancelBot();
            gM.g.undo();
        } else {
            if (!gM.g.undo()) return;
            if (gM.g.cur.side != gM.human && !gM.g.moves.empty()) gM.g.undo();
        }
    } else {
        if (!gM.g.undo()) return;
        gResultPending = false;
    }
    gAnims.clear();
    clearSel();
    gViewSide = gM.g.cur.side;
    gListScroll = 0;
    gViewPly = -1;
    clearUserMarks();
    playSound(SND_CLICK);
    saveAll();
    startBot();
}

static bool canUndo() {
    if (!gM.active || gM.g.moves.empty() || gM.mode == MODE_NET) return false;
    if (gM.mode == MODE_BOT) {
        if (gM.g.result != RES_NONE) return false;
        if (botThinking()) return true;
        if (gM.g.cur.side == gM.human) {
            // отменяем пару ходов: бота и свой (если первым ходил бот — его ход не отменить)
            return gM.g.moves.size() >= 2;
        }
        return true;
    }
    return true;
}

static void doResign() {
    if (!gM.active || gM.g.result != RES_NONE) return;
    int loser = gM.mode != MODE_TWO ? gM.human : gM.g.cur.side;
    if (gM.mode == MODE_NET) netSendLine("RESIGN");
    gM.g.result = loser == eng::WHITE ? RES_BLACK : RES_WHITE;
    gM.g.reason = R_RESIGN;
    gM.g.loser = loser;
    onGameEnd();
}

static void onTimeout(int side) {
    gM.tLeft[side] = 0;
    cancelBot();
    if (gM.g.cur.canMate(side ^ 1)) gM.g.result = side == eng::WHITE ? RES_BLACK : RES_WHITE;
    else gM.g.result = RES_DRAW;
    gM.g.reason = R_TIME;
    gM.g.loser = side;
    onGameEnd();
}

static bool canHumanMove() {
    if (gScreen != SC_GAME || !gM.active || gM.g.result != RES_NONE || gOverlay != OV_NONE || viewing()) return false;
    if (gM.mode == MODE_BOT) return !botThinking() && gM.g.cur.side == gM.human;
    if (gM.mode == MODE_NET) return netConnected() && gM.g.cur.side == gM.human;
    return true;
}

// =====================================================================
//                     ОБУЧЕНИЕ: УРОКИ И ЗАДАЧИ
// =====================================================================
// Режимы страницы: показ позиции, «попробуй походить» фигурой, задача.
enum { LM_SHOW = 0, LM_MOVES = 1, LM_PUZZLE = 2, LM_GAME = 3 };
struct LPage {
    const char *title;
    const char *fen;
    const char *marks;  // «e4:g» — подсветка (g/r/y/b), «c4>f7» — стрелка
    int mode;
    const char *sol;    // LM_MOVES: поле фигуры; LM_PUZZLE: ход «e4f6» или «#» (любой мат)
    const char *text;
};
struct LChapter {
    const char *title;
    const char *sub;
    const LPage *pages;
    int n;
};

#define FEN_START "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define FEN_ITALIAN "r1bqkbnr/pppp1ppp/2n5/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R b KQkq - 3 3"

static const LPage LP_BASICS[] = {
    {"ШАХМАТНАЯ ДОСКА", FEN_START, "h1:g a1:y", LM_SHOW, "",
     "ДОСКА СОСТОИТ ИЗ 64 КЛЕТОК. ВЕРТИКАЛИ ОБОЗНАЧАЮТ БУКВАМИ ОТ a ДО h, ГОРИЗОНТАЛИ - ЦИФРАМИ ОТ 1 ДО 8. "
     "У КАЖДОЙ КЛЕТКИ ЕСТЬ ИМЯ, НАПРИМЕР e4.\n"
     "ДОСКУ КЛАДУТ ТАК, ЧТОБЫ СПРАВА ВНИЗУ У ИГРОКА БЫЛА СВЕТЛАЯ КЛЕТКА h1."},
    {"РАССТАНОВКА", FEN_START, "d1:g d8:g e1:y e8:y", LM_SHOW, "",
     "ЛАДЬИ СТОЯТ В УГЛАХ, РЯДОМ С НИМИ КОНИ, ЗАТЕМ СЛОНЫ. ФЕРЗЬ ЗАНИМАЕТ ПОЛЕ СВОЕГО ЦВЕТА: "
     "БЕЛЫЙ - d1, ЧЁРНЫЙ - d8. КОРОЛИ СТОЯТ НА e1 И e8. ВПЕРЕДИ - ВОСЕМЬ ПЕШЕК.\n"
     "ПЕРВЫЙ ХОД ДЕЛАЮТ БЕЛЫЕ, ДАЛЬШЕ ИГРОКИ ХОДЯТ ПО ОЧЕРЕДИ. ПРОПУСТИТЬ ХОД НЕЛЬЗЯ."},
    {"ЦЕЛЬ ИГРЫ", "3R2k1/5ppp/8/8/8/8/5PPP/6K1 b - - 0 1", "g8:r d8>g8", LM_SHOW, "",
     "ЦЕЛЬ ШАХМАТ - ПОСТАВИТЬ МАТ КОРОЛЮ СОПЕРНИКА: НАПАСТЬ НА НЕГО ТАК, ЧТОБЫ ОН НЕ СМОГ СПАСТИСЬ. "
     "КОРОЛЯ НЕ СЪЕДАЮТ - ПАРТИЯ ЗАКАНЧИВАЕТСЯ В МОМЕНТ МАТА.\n"
     "НА ДИАГРАММЕ БЕЛАЯ ЛАДЬЯ ПОСТАВИЛА МАТ: ЧЁРНОМУ КОРОЛЮ НЕКУДА УЙТИ."},
};

static const LPage LP_PIECES[] = {
    {"ПЕШКА", "4k3/8/8/8/8/8/4P3/4K3 w - - 0 1", "", LM_MOVES, "e2",
     "ПЕШКА ХОДИТ ТОЛЬКО ВПЕРЁД НА ОДНУ КЛЕТКУ. СО СВОЕГО НАЧАЛЬНОГО ПОЛЯ ОНА МОЖЕТ ПРОЙТИ СРАЗУ НА ДВЕ. "
     "НАЗАД ПЕШКИ НЕ ХОДЯТ.\nНАЖИМАЙТЕ НА ТОЧКИ, ЧТОБЫ ПОХОДИТЬ."},
    {"ПЕШКА БЬЁТ", "4k3/8/8/3p1n2/4P3/8/8/4K3 w - - 0 1", "", LM_MOVES, "e4",
     "ПЕШКА БЬЁТ НЕ ТАК, КАК ХОДИТ: НАИСКОСОК НА ОДНУ КЛЕТКУ ВПЕРЁД. ЗДЕСЬ ПЕШКА e4 МОЖЕТ ВЗЯТЬ ПЕШКУ d5 "
     "ИЛИ КОНЯ f5. ФИГУРУ ПРЯМО ПЕРЕД СОБОЙ ПЕШКА ВЗЯТЬ НЕ МОЖЕТ."},
    {"КОНЬ", "4k3/8/8/8/3N4/8/8/4K3 w - - 0 1", "", LM_MOVES, "d4",
     "КОНЬ ХОДИТ БУКВОЙ Г: ДВЕ КЛЕТКИ ПО ПРЯМОЙ И ОДНА В СТОРОНУ. ЭТО ЕДИНСТВЕННАЯ ФИГУРА, КОТОРАЯ "
     "ПЕРЕПРЫГИВАЕТ ЧЕРЕЗ ДРУГИЕ.\nВ ЦЕНТРЕ КОНЬ АТАКУЕТ 8 ПОЛЕЙ, А В УГЛУ - ВСЕГО 2. ПОЭТОМУ ГОВОРЯТ: "
     "КОНЬ НА КРАЮ - ДОСКЕ ГОРЕ."},
    {"СЛОН", "4k3/8/8/8/3B4/8/8/4K3 w - - 0 1", "", LM_MOVES, "d4",
     "СЛОН ХОДИТ ПО ДИАГОНАЛИ НА ЛЮБОЕ РАССТОЯНИЕ, НО НЕ ПЕРЕПРЫГИВАЕТ ФИГУРЫ. ВСЮ ПАРТИЮ СЛОН ОСТАЁТСЯ "
     "НА ПОЛЯХ ОДНОГО ЦВЕТА, ПОЭТОМУ У КАЖДОГО ИГРОКА ЕСТЬ БЕЛОПОЛЬНЫЙ И ЧЕРНОПОЛЬНЫЙ СЛОН."},
    {"ЛАДЬЯ", "4k3/8/8/8/3R4/8/8/4K3 w - - 0 1", "", LM_MOVES, "d4",
     "ЛАДЬЯ ХОДИТ ПО ВЕРТИКАЛИ И ГОРИЗОНТАЛИ НА ЛЮБОЕ РАССТОЯНИЕ. ОНА ОСОБЕННО СИЛЬНА НА ОТКРЫТЫХ "
     "ЛИНИЯХ, ГДЕ НЕТ ПЕШЕК, И НА ПРЕДПОСЛЕДНЕЙ ГОРИЗОНТАЛИ СОПЕРНИКА."},
    {"ФЕРЗЬ", "4k3/8/8/8/3Q4/8/8/4K3 w - - 0 1", "", LM_MOVES, "d4",
     "ФЕРЗЬ - САМАЯ СИЛЬНАЯ ФИГУРА: ОН ХОДИТ И КАК ЛАДЬЯ, И КАК СЛОН. НО НЕ СПЕШИТЕ ВЫВОДИТЬ ЕГО В "
     "НАЧАЛЕ ПАРТИИ: СОПЕРНИК БУДЕТ НАПАДАТЬ НА ФЕРЗЯ ЛЁГКИМИ ФИГУРАМИ И ВЫИГРЫВАТЬ ВРЕМЯ."},
    {"КОРОЛЬ", "8/8/8/8/3K4/8/8/7k w - - 0 1", "", LM_MOVES, "d4",
     "КОРОЛЬ ХОДИТ НА ОДНУ КЛЕТКУ В ЛЮБУЮ СТОРОНУ. СТАВИТЬ КОРОЛЯ ПОД УДАР НЕЛЬЗЯ, ПОЭТОМУ ДВА КОРОЛЯ "
     "НИКОГДА НЕ СТОЯТ РЯДОМ. БЕРЕГИТЕ КОРОЛЯ: МАТ ЕМУ - ЭТО ПРОИГРЫШ."},
};

static const LPage LP_SPECIAL[] = {
    {"РОКИРОВКА", "r3k2r/pppppppp/8/8/8/8/PPPPPPPP/R3K2R w KQkq - 0 1", "", LM_MOVES, "e1",
     "РОКИРОВКА - ХОД КОРОЛЁМ И ЛАДЬЁЙ СРАЗУ. КОРОЛЬ ИДЁТ НА ДВЕ КЛЕТКИ К ЛАДЬЕ, А ЛАДЬЯ ПЕРЕПРЫГИВАЕТ "
     "ЧЕРЕЗ НЕГО. КОРОЛЬ ПРЯЧЕТСЯ, А ЛАДЬЯ ВСТУПАЕТ В ИГРУ.\n"
     "УСЛОВИЯ: КОРОЛЬ И ЛАДЬЯ ЕЩЁ НЕ ХОДИЛИ, МЕЖДУ НИМИ ПУСТО, КОРОЛЬ НЕ ПОД ШАХОМ И НЕ ПРОХОДИТ ЧЕРЕЗ "
     "АТАКОВАННОЕ ПОЛЕ.\nВ ИГРЕ ПРОСТО ПЕРЕДВИНЬТЕ КОРОЛЯ НА ДВЕ КЛЕТКИ."},
    {"ВЗЯТИЕ НА ПРОХОДЕ", "4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 1", "d7>d5", LM_MOVES, "e5",
     "ЕСЛИ ПЕШКА СОПЕРНИКА СДЕЛАЛА ДВОЙНОЙ ШАГ И ВСТАЛА РЯДОМ С ВАШЕЙ ПЕШКОЙ, ЕЁ МОЖНО ВЗЯТЬ ТАК, БУДТО "
     "ОНА ПРОШЛА ОДНУ КЛЕТКУ. ЗДЕСЬ ЧЁРНЫЕ СЫГРАЛИ d7-d5, И БЕЛЫЕ МОГУТ БИТЬ exd6.\n"
     "ТАК БРАТЬ МОЖНО ТОЛЬКО СРАЗУ, СЛЕДУЮЩИМ ХОДОМ."},
    {"ПРЕВРАЩЕНИЕ ПЕШКИ", "8/4P3/8/8/8/k7/8/4K3 w - - 0 1", "", LM_MOVES, "e7",
     "ПЕШКА, ДОШЕДШАЯ ДО ПОСЛЕДНЕЙ ГОРИЗОНТАЛИ, ПРЕВРАЩАЕТСЯ В ЛЮБУЮ ФИГУРУ, КРОМЕ КОРОЛЯ. ЧАЩЕ ВСЕГО "
     "ВЫБИРАЮТ ФЕРЗЯ. ПОЭТОМУ ПРОХОДНАЯ ПЕШКА, КОТОРУЮ НЕ МОГУТ ОСТАНОВИТЬ ПЕШКИ СОПЕРНИКА, ОЧЕНЬ ОПАСНА."},
};

static const LPage LP_ENDING[] = {
    {"ШАХ", "4k3/8/8/8/8/8/8/4R1K1 b - - 0 1", "e1>e8", LM_SHOW, "",
     "ШАХ - ЭТО НАПАДЕНИЕ НА КОРОЛЯ. НА ШАХ НУЖНО ОТВЕТИТЬ СРАЗУ ОДНИМ ИЗ ТРЁХ СПОСОБОВ:\n"
     "1. УЙТИ КОРОЛЁМ НА БЕЗОПАСНОЕ ПОЛЕ.\n2. ЗАКРЫТЬСЯ ДРУГОЙ ФИГУРОЙ.\n3. ВЗЯТЬ ФИГУРУ, КОТОРАЯ ДАЁТ ШАХ."},
    {"МАТ", "3R2k1/5ppp/8/8/8/8/5PPP/6K1 b - - 0 1", "f7:y g7:y h7:y", LM_SHOW, "",
     "МАТ - ЭТО ШАХ, ОТ КОТОРОГО НЕТ ЗАЩИТЫ. ЗДЕСЬ ЧЁРНОГО КОРОЛЯ ЗАПЕРЛИ ЕГО СОБСТВЕННЫЕ ПЕШКИ. ЭТО МАТ "
     "ПО ПОСЛЕДНЕЙ ГОРИЗОНТАЛИ - ОДНА ИЗ САМЫХ ЧАСТЫХ ОШИБОК.\n"
     "СОВЕТ: ЗАРАНЕЕ ОСВОБОДИТЕ КОРОЛЮ ПОЛЕ, ПОДВИНУВ ПЕШКУ h ИЛИ g."},
    {"ПАТ", "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1", "h8:y", LM_SHOW, "",
     "ПАТ - КОГДА ИГРОКУ НЕКУДА ХОДИТЬ, НО ЕГО КОРОЛЬ НЕ ПОД ШАХОМ. ПАТ - ЭТО НИЧЬЯ! ЗДЕСЬ ЧЁРНЫЕ НЕ МОГУТ "
     "СДЕЛАТЬ НИ ОДНОГО ХОДА.\nКОГДА У ВАС БОЛЬШОЙ ПЕРЕВЕС, ВСЕГДА ПРОВЕРЯЙТЕ, ЧТО У КОРОЛЯ СОПЕРНИКА "
     "ОСТАЛСЯ ХОД."},
    {"ДРУГИЕ НИЧЬИ", "8/8/4k3/8/8/3KB3/8/8 w - - 0 1", "", LM_SHOW, "",
     "НИЧЬЯ БЫВАЕТ ТАКЖЕ:\n- ПРИ НЕДОСТАТКЕ МАТЕРИАЛА: КОРОЛЬ С ОДНИМ СЛОНОМ ИЛИ КОНЁМ НЕ МОЖЕТ ДАТЬ МАТ;\n"
     "- ПРИ ТРОЕКРАТНОМ ПОВТОРЕНИИ ОДНОЙ И ТОЙ ЖЕ ПОЗИЦИИ;\n"
     "- ЕСЛИ 50 ХОДОВ ПОДРЯД НЕ БЫЛО НИ ВЗЯТИЙ, НИ ХОДОВ ПЕШКАМИ."},
};

static const LPage LP_VALUE[] = {
    {"ЦЕННОСТЬ ФИГУР", "4k3/8/8/8/1P1N1B1R/3Q4/8/4K3 w - - 0 1", "", LM_SHOW, "",
     "ПРИМЕРНАЯ ЦЕНА ФИГУР В ПЕШКАХ:\nПЕШКА = 1\nКОНЬ = 3, СЛОН = 3\nЛАДЬЯ = 5\nФЕРЗЬ = 9\n"
     "КОРОЛЬ БЕСЦЕНЕН.\nПЕРЕД ОБМЕНОМ СЧИТАЙТЕ: ОТДАТЬ КОНЯ ЗА ПЕШКУ ИЛИ ЛАДЬЮ ЗА КОНЯ - НЕВЫГОДНО. "
     "ДВА СЛОНА ОБЫЧНО СИЛЬНЕЕ СЛОНА И КОНЯ."},
    {"НЕ ЗЕВАЙТЕ ФИГУРЫ", "4k3/pp3ppp/8/3q4/8/2N5/PP3PPP/4K3 w - - 0 1", "", LM_PUZZLE, "c3d5",
     "ПЕРЕД КАЖДЫМ ХОДОМ ПРОВЕРЯЙТЕ, НЕТ ЛИ НА ДОСКЕ НЕЗАЩИЩЁННЫХ ФИГУР - СВОИХ И ЧУЖИХ.\n"
     "ЗАДАЧА: ЧЁРНЫЕ ЗЕВНУЛИ ФЕРЗЯ. ЗАБЕРИТЕ ЕГО."},
};

static const LPage LP_OPENING[] = {
    {"ПРИНЦИПЫ ДЕБЮТА", FEN_ITALIAN, "e4:g d4:g e5:g d5:g", LM_SHOW, "",
     "1. ЗАНИМАЙТЕ ЦЕНТР ПЕШКАМИ: e4 И d4.\n2. БЫСТРО ВЫВОДИТЕ КОНЕЙ И СЛОНОВ.\n"
     "3. СДЕЛАЙТЕ РОКИРОВКУ, ЧТОБЫ СПРЯТАТЬ КОРОЛЯ.\n4. НЕ ХОДИТЕ ОДНОЙ ФИГУРОЙ ДВАЖДЫ БЕЗ НУЖДЫ.\n"
     "5. ФЕРЗЯ ВЫВОДИТЕ ПОСЛЕ КОНЕЙ И СЛОНОВ."},
    {"ИТАЛЬЯНСКАЯ ПАРТИЯ", FEN_ITALIAN, "c4>f7 f3>e5", LM_SHOW, "",
     "1.e4 e5 2.Кf3 Кc6 3.Сc4\nБЕЛЫЕ ЗАНЯЛИ ЦЕНТР, КОНЬ НАПАДАЕТ НА ПЕШКУ e5, А СЛОН НАЦЕЛЕН НА СЛАБОЕ "
     "ПОЛЕ f7, КОТОРОЕ ЗАЩИЩАЕТ ТОЛЬКО КОРОЛЬ. ОТЛИЧНЫЙ ДЕБЮТ ДЛЯ НАЧИНАЮЩИХ."},
    {"ДЕТСКИЙ МАТ", "r1bqkb1r/pppp1Qpp/2n2n2/4p3/2B1P3/8/PPPP1PPP/RNB1K1NR b KQkq - 0 4", "e8:r c4>f7", LM_SHOW, "",
     "ЛОВУШКА ДЛЯ НОВИЧКОВ: ФЕРЗЬ И СЛОН ВМЕСТЕ БЬЮТ НА f7. МАТ УЖЕ НА 4-М ХОДУ.\n"
     "ЗАЩИТА: ВОВРЕМЯ ПРИКРОЙТЕ f7, НАПРИМЕР ХОДОМ g6 ИЛИ Фe7, И НАПАДАЙТЕ НА РАНО ВЫШЕДШЕГО ФЕРЗЯ."},
    {"ЗАДАЧА: ДЕТСКИЙ МАТ", "r1bqkb1r/pppp1ppp/2n2n2/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w KQkq - 4 4", "", LM_PUZZLE, "#",
     "ЧЁРНЫЕ ОШИБЛИСЬ, СЫГРАВ Кf6 ВМЕСТО ЗАЩИТЫ. ПОСТАВЬТЕ МАТ В ОДИН ХОД."},
    {"ЧЕГО ИЗБЕГАТЬ", FEN_START, "", LM_SHOW, "",
     "- НЕ ДВИГАЙТЕ МНОГО ПЕШЕК НА КРАЯХ ДОСКИ.\n- НЕ ВЫВОДИТЕ ФЕРЗЯ СЛИШКОМ РАНО.\n"
     "- НЕ ОСТАВЛЯЙТЕ КОРОЛЯ В ЦЕНТРЕ.\n- НЕ ГОНИТЕСЬ ЗА ПЕШКАМИ, ПОКА ФИГУРЫ НЕ ВЫВЕДЕНЫ.\n"
     "- НЕ ЗАПИРАЙТЕ СВОИХ СЛОНОВ СОБСТВЕННЫМИ ПЕШКАМИ."},
};

static const LPage LP_TACTICS[] = {
    {"ВИЛКА", "6k1/3q4/8/8/4N3/8/8/4K3 w - - 0 1", "", LM_PUZZLE, "e4f6",
     "ВИЛКА - ОДНА ФИГУРА НАПАДАЕТ СРАЗУ НА ДВЕ. СОПЕРНИК СПАСЁТ ТОЛЬКО ОДНУ. КОНЬ - МАСТЕР ВИЛОК.\n"
     "ЗАДАЧА: НАЙДИТЕ ХОД КОНЁМ С ШАХОМ, ЧТОБЫ ВЫИГРАТЬ ФЕРЗЯ."},
    {"СВЯЗКА", "4k3/8/4n3/8/8/8/8/4R1K1 w - - 0 1", "e1>e8 e6:r", LM_SHOW, "",
     "СВЯЗКА: КОНЬ e6 НЕ МОЖЕТ УЙТИ, ПОТОМУ ЧТО ЗА НИМ СТОИТ КОРОЛЬ - ОТКРЫВАТЬ КОРОЛЯ ПОД ШАХ НЕЛЬЗЯ. "
     "СВЯЗАННАЯ ФИГУРА БЕСПОМОЩНА: ЕЁ МОЖНО АТАКОВАТЬ ЕЩЁ РАЗ, НАПРИМЕР ПЕШКОЙ."},
    {"ЗАДАЧА: СВЯЗКА", "4k3/8/4n3/8/3P4/8/8/4R1K1 w - - 0 1", "", LM_PUZZLE, "d4d5",
     "КОНЬ e6 СВЯЗАН ЛАДЬЁЙ. НАПАДИТЕ НА НЕГО ПЕШКОЙ - ОН НЕ СМОЖЕТ УЙТИ."},
    {"СКВОЗНОЙ УДАР", "8/8/2k4q/8/8/8/8/R5K1 w - - 0 1", "", LM_PUZZLE, "a1a6",
     "СКВОЗНОЙ УДАР: ШАХ КОРОЛЮ, А ЗА НИМ НА ТОЙ ЖЕ ЛИНИИ СТОИТ ЦЕННАЯ ФИГУРА. КОРОЛЬ УХОДИТ - ФИГУРА "
     "ГИБНЕТ.\nЗАДАЧА: ВЫИГРАЙТЕ ФЕРЗЯ ЧЁРНЫХ."},
    {"МАТ НА ПОСЛЕДНЕЙ ГОРИЗОНТАЛИ", "6k1/5ppp/8/8/8/8/5PPP/3R2K1 w - - 0 1", "", LM_PUZZLE, "#",
     "КОРОЛЬ ЧЁРНЫХ ЗАПЕРТ СВОИМИ ПЕШКАМИ. ПОСТАВЬТЕ МАТ В ОДИН ХОД."},
    {"СПЁРТЫЙ МАТ", "6rk/6pp/8/6N1/8/8/8/7K w - - 0 1", "", LM_PUZZLE, "#",
     "КОРОЛЮ МЕШАЮТ СОБСТВЕННЫЕ ФИГУРЫ. КОНЬ ПЕРЕПРЫГИВАЕТ ЧЕРЕЗ ЛЮБУЮ ЗАЩИТУ. МАТ В ОДИН ХОД."},
};

static const LPage LP_ENDGAME[] = {
    {"АКТИВНЫЙ КОРОЛЬ", "8/5k2/8/3K4/8/8/5P2/8 w - - 0 1", "d5:g", LM_SHOW, "",
     "В ЭНДШПИЛЕ, КОГДА ФЕРЗЕЙ УЖЕ НЕТ, КОРОЛЬ СТАНОВИТСЯ СИЛЬНОЙ ФИГУРОЙ. ВЕДИТЕ ЕГО В ЦЕНТР И "
     "ПОМОГАЙТЕ ПЕШКАМ. ПРОХОДНЫЕ ПЕШКИ НАДО ДВИГАТЬ ВПЕРЁД - ОНИ МОГУТ СТАТЬ ФЕРЗЯМИ."},
    {"МАТ ФЕРЗЁМ", "8/8/8/4k3/8/8/8/3QK3 w - - 0 1", "", LM_SHOW, "",
     "ФЕРЗЁМ ОТРЕЗАЙТЕ КОРОЛЮ СОПЕРНИКА ПОЛЯ, СУЖАЯ ЕГО КЛЕТКУ, ПОКА ОН НЕ ОКАЖЕТСЯ НА КРАЮ ДОСКИ. "
     "ЗАТЕМ ПОДВЕДИТЕ СВОЕГО КОРОЛЯ И ДАЙТЕ МАТ.\nОСТОРОЖНО: НЕ ЗАБИРАЙТЕ У КОРОЛЯ ВСЕ ХОДЫ БЕЗ ШАХА - "
     "ЭТО ПАТ И НИЧЬЯ!"},
    {"ЗАДАЧА: ФЕРЗЬ", "k7/8/2K5/8/8/8/8/1Q6 w - - 0 1", "", LM_PUZZLE, "#",
     "КОРОЛЬ ЧЁРНЫХ В УГЛУ. ФЕРЗЮ НУЖНА ПОДДЕРЖКА КОРОЛЯ. НАЙДИТЕ МАТ В ОДИН ХОД."},
    {"ЗАДАЧА: ЛАДЬЯ", "k7/8/1K6/8/8/8/8/7R w - - 0 1", "", LM_PUZZLE, "#",
     "КОРОЛЬ ЧЁРНЫХ ПРИЖАТ К КРАЮ, ВАШ КОРОЛЬ НЕ ДАЁТ ЕМУ ВЫЙТИ. ПОСТАВЬТЕ МАТ ЛАДЬЁЙ."},
    {"ОППОЗИЦИЯ", "4k3/8/4K3/4P3/8/8/8/8 b - - 0 1", "e8:y e6:y", LM_SHOW, "",
     "КОРОЛИ СТОЯТ ДРУГ НАПРОТИВ ДРУГА ЧЕРЕЗ КЛЕТКУ - ЭТО ОППОЗИЦИЯ. ТОТ, КТО ДОЛЖЕН ХОДИТЬ, ВЫНУЖДЕН "
     "УСТУПИТЬ ДОРОГУ. ЗДЕСЬ ХОДЯТ ЧЁРНЫЕ, И БЕЛАЯ ПЕШКА ПРОЙДЁТ В ФЕРЗИ."},
};

static const LPage LP_STRATEGY[] = {
    {"МЫСЛИ ПЕРЕД ХОДОМ", FEN_ITALIAN, "", LM_SHOW, "",
     "КАЖДЫЙ ХОД ЗАДАВАЙТЕ СЕБЕ 4 ВОПРОСА:\n1. ЧТО ХОЧЕТ СОПЕРНИК СВОИМ ПОСЛЕДНИМ ХОДОМ?\n"
     "2. ЕСТЬ ЛИ У МЕНЯ ШАХИ, ВЗЯТИЯ И УГРОЗЫ?\n3. КАКАЯ МОЯ ФИГУРА СТОИТ ХУЖЕ ВСЕХ? УЛУЧШИТЕ ЕЁ.\n"
     "4. НЕ ОСТАВЛЯЮ ЛИ Я ФИГУРУ БЕЗ ЗАЩИТЫ?"},
    {"ОТКРЫТЫЕ ЛИНИИ", "6k1/pp3ppp/2n5/8/8/2N5/PP3PPP/3R2K1 w - - 0 1", "d1>d7 d7:g", LM_SHOW, "",
     "ЛАДЬИ СТАВЬТЕ НА ОТКРЫТЫЕ ВЕРТИКАЛИ, ГДЕ НЕТ ПЕШЕК. ЛАДЬЯ, ВОРВАВШАЯСЯ НА 7-Ю ГОРИЗОНТАЛЬ, "
     "НАПАДАЕТ НА ПЕШКИ И ЗАПИРАЕТ КОРОЛЯ."},
    {"ПЕШЕЧНАЯ СТРУКТУРА", "4k3/pp4pp/8/8/8/2P5/P1P2PPP/4K3 w - - 0 1", "c2:r c3:r", LM_SHOW, "",
     "ПЕШКИ НЕ ХОДЯТ НАЗАД, ПОЭТОМУ КАЖДЫЙ ПЕШЕЧНЫЙ ХОД - РЕШЕНИЕ НАВСЕГДА. ИЗБЕГАЙТЕ СДВОЕННЫХ ПЕШЕК "
     "(ДВЕ НА ОДНОЙ ВЕРТИКАЛИ, КАК НА c2 И c3) И ИЗОЛИРОВАННЫХ - БЕЗ СОСЕДЕЙ. ДЕРЖИТЕ ПЕШКИ ЦЕПОЧКОЙ, "
     "ЧТОБЫ ОНИ ЗАЩИЩАЛИ ДРУГ ДРУГА."},
    {"КОГДА МЕНЯТЬСЯ", "r4rk1/pp3ppp/2n5/8/8/2N5/PP3PPP/R4RK1 w - - 0 1", "", LM_SHOW, "",
     "ЕСЛИ ВЫ ВПЕРЕДИ ПО МАТЕРИАЛУ - МЕНЯЙТЕ ФИГУРЫ: ЧЕМ МЕНЬШЕ ФИГУР, ТЕМ ЗАМЕТНЕЕ ПЕРЕВЕС. "
     "ЕСЛИ ОТСТАЁТЕ - ИЗБЕГАЙТЕ РАЗМЕНОВ И ИЩИТЕ АТАКУ. НЕ МЕНЯЙТЕ АКТИВНУЮ ФИГУРУ НА ПАССИВНУЮ."},
    {"КАК ИГРАТЬ С БОТОМ", FEN_START, "", LM_SHOW, "",
     "НАЧНИТЕ С УРОВНЯ 1 ИЛИ 2. ВЫИГРАЛИ НЕСКОЛЬКО РАЗ ПОДРЯД - ПОВЫШАЙТЕ УРОВЕНЬ.\n"
     "ЗЕВНУЛИ ФИГУРУ - НАЖМИТЕ ОТМЕНА И ПОДУМАЙТЕ ЕЩЁ.\nПОСЛЕ ПАРТИИ ПРОСМОТРИТЕ ЗАПИСЬ ХОДОВ И "
     "НАЙДИТЕ, ГДЕ БЫЛА ОШИБКА.\nИГРАЙТЕ С ЧАСАМИ, ЧТОБЫ НАУЧИТЬСЯ РАСПРЕДЕЛЯТЬ ВРЕМЯ."},
};

static const LPage LP_NOTATION[] = {
    {"ЗАПИСЬ ХОДОВ", FEN_ITALIAN, "f3:g c4:g", LM_SHOW, "",
     "В СПИСКЕ ХОДОВ ФИГУРЫ ОБОЗНАЧАЮТ БУКВАМИ:\nКр - КОРОЛЬ, Ф - ФЕРЗЬ, Л - ЛАДЬЯ, С - СЛОН, К - КОНЬ. "
     "У ПЕШКИ БУКВЫ НЕТ.\nКf3 - КОНЬ ПОШЁЛ НА f3.\nexd5 - ПЕШКА e ВЗЯЛА НА d5.\n"
     "x - ВЗЯТИЕ, + - ШАХ, # - МАТ.\n0-0 - КОРОТКАЯ РОКИРОВКА, 0-0-0 - ДЛИННАЯ."},
};

// Тактика на примерах: партия с приёмом (LM_GAME) + задача, где приём применяет игрок.
// Для LM_GAME: marks — комментарии «номер_полухода|текст|...», sol — ходы партии.
// Для задач sol — ходы через пробел: ваш, ответ соперника, ваш... («#» — любой мат).
static const LPage LP_TACT2[] = {
    {"ВИЛКА: ПРИМЕР", FEN_START,
     "5|СЛОН НАЦЕЛИЛСЯ НА СЛАБОЕ ПОЛЕ f7, ЕГО ЗАЩИЩАЕТ ТОЛЬКО КОРОЛЬ.|7|КОНЬ ТОЖЕ НАПАДАЕТ НА f7. УГРОЗА ДВОЙНАЯ!|"
     "10|ОШИБКА ЧЁРНЫХ: ПРАВИЛЬНО БЫЛО Кa5, УБИРАЯ КОНЯ С ДОРОГИ И НАПАДАЯ НА СЛОНА.|"
     "11|ВИЛКА! КОНЬ НА f7 НАПАДАЕТ СРАЗУ НА ФЕРЗЯ d8 И ЛАДЬЮ h8. ЧЁРНЫЕ ПОТЕРЯЮТ МАТЕРИАЛ. ЭТО ДЕБЮТ ЖАРЕНАЯ ПЕЧЁНКА.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1c4 g8f6 f3g5 d7d5 e4d5 f6d5 g5f7",
     "ВИЛКА - ОДНА ФИГУРА НАПАДАЕТ НА ДВЕ ЦЕЛИ СРАЗУ. ПОСМОТРИТЕ, КАК ЭТО БЫВАЕТ В НАСТОЯЩЕЙ ПАРТИИ."},
    {"ВИЛКА: ВАШ ХОД", "6k1/3q4/8/8/4N3/8/8/4K3 w - - 0 1", "", LM_PUZZLE, "e4f6 g8g7 f6d7",
     "ТЕПЕРЬ САМИ. НАЙДИТЕ ХОД КОНЁМ С ШАХОМ, КОТОРЫЙ НАПАДАЕТ ЕЩЁ И НА ФЕРЗЯ. ПОСЛЕ ОТВЕТА СОПЕРНИКА "
     "ЗАБЕРИТЕ ФЕРЗЯ."},
    {"ДВОЙНОЙ УДАР: ПРИМЕР", FEN_START,
     "9|КАЖЕТСЯ, БЕЛЫЕ ПРОСТО ОТДАЛИ КОНЯ ЗА ПЕШКУ...|10|ЧЁРНЫЕ ВЗЯЛИ КОНЯ.|"
     "11|ДВОЙНОЙ УДАР ПЕШКОЙ! d4 НАПАДАЕТ НА СЛОНА c5 И КОНЯ e5. ОДНА ИЗ ФИГУР ПОГИБНЕТ, И БЕЛЫЕ ОТЫГРЫВАЮТ "
     "МАТЕРИАЛ С ХОРОШИМ ЦЕНТРОМ. ЭТОТ ПРИЁМ НАЗЫВАЮТ ТРЮК С ВИЛКОЙ.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 b1c3 g8f6 f3e5 c6e5 d2d4",
     "ДВОЙНОЙ УДАР - НАПАДЕНИЕ НА ДВЕ ФИГУРЫ ОДНИМ ХОДОМ. ЕГО МОЖЕТ НАНЕСТИ ЛЮБАЯ ФИГУРА, ДАЖЕ ПЕШКА."},
    {"ДВОЙНОЙ УДАР: ВАШ ХОД", "r5k1/6pp/8/8/8/8/5PPP/3Q2K1 w - - 0 1", "", LM_PUZZLE, "d1d5 g8h8 d5a8",
     "ЛАДЬЯ ЧЁРНЫХ НА a8 НЕ ЗАЩИЩЕНА. НАЙДИТЕ ХОД ФЕРЗЁМ, КОТОРЫЙ ДАЁТ ШАХ И ОДНОВРЕМЕННО НАПАДАЕТ НА ЛАДЬЮ."},
    {"СВЯЗКА: ПРИМЕР", FEN_START,
     "10|ЧЁРНЫЕ ВЗЯЛИ ПЕШКУ КОНЁМ...|11|...НО ЛАДЬЯ ВСТАЛА НА ЛИНИЮ e. КОНЬ e4 СВЯЗАН: ЗА НИМ СТОИТ КОРОЛЬ.|"
     "15|Кc3 НАПАДАЕТ НА ФЕРЗЯ И НА СВЯЗАННОГО КОНЯ. ФЕРЗЬ УЙДЁТ, А КОНЬ ОСТАНЕТСЯ ПОД УДАРОМ - БЕЛЫЕ "
     "ОТЫГРЫВАЮТ ФИГУРУ.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1c4 g8f6 d2d4 e5d4 e1g1 f6e4 f1e1 d7d5 c4d5 d8d5 b1c3",
     "СВЯЗКА - ФИГУРА НЕ МОЖЕТ ОТОЙТИ, ПОТОМУ ЧТО ЗА НЕЙ СТОИТ КОРОЛЬ ИЛИ ЦЕННАЯ ФИГУРА. НА СВЯЗАННУЮ "
     "ФИГУРУ ВЫГОДНО НАПАДАТЬ ЕЩЁ РАЗ."},
    {"СВЯЗКА: ВАШ ХОД", "4k3/8/4n3/8/3P4/8/8/4R1K1 w - - 0 1", "", LM_PUZZLE, "d4d5 e8f7 d5e6",
     "КОНЬ e6 СВЯЗАН ЛАДЬЁЙ. НАПАДИТЕ НА НЕГО ПЕШКОЙ, А ПОСЛЕ ОТВЕТА СОПЕРНИКА ЗАБЕРИТЕ КОНЯ."},
    {"СКВОЗНОЙ УДАР: ПРИМЕР", "7q/8/3k4/8/8/8/8/2B3K1 b - - 0 1",
     "1|ЧЁРНЫЕ НЕОСТОРОЖНО ПОСТАВИЛИ КОРОЛЯ НА ОДНУ ДИАГОНАЛЬ СО СВОИМ ФЕРЗЁМ.|"
     "2|СКВОЗНОЙ УДАР! СЛОН ДАЁТ ШАХ, А ЗА КОРОЛЁМ НА ТОЙ ЖЕ ЛИНИИ СТОИТ ФЕРЗЬ.|3|КОРОЛЬ ОБЯЗАН УЙТИ ОТ ШАХА...|"
     "4|...И СЛОН ЗАБИРАЕТ ФЕРЗЯ.",
     LM_GAME, "d6e5 c1b2 e5e6 b2h8",
     "СКВОЗНОЙ УДАР ПОХОЖ НА СВЯЗКУ НАОБОРОТ: НАПАДАЮТ НА ЦЕННУЮ ФИГУРУ, ОНА УХОДИТ, И ОТКРЫВАЕТСЯ ДРУГАЯ."},
    {"СКВОЗНОЙ УДАР: ВАШ ХОД", "8/8/2k4q/8/8/8/8/R5K1 w - - 0 1", "", LM_PUZZLE, "a1a6 c6c7 a6h6",
     "КОРОЛЬ И ФЕРЗЬ ЧЁРНЫХ СТОЯТ НА ОДНОЙ ГОРИЗОНТАЛИ. ДАЙТЕ ШАХ ЛАДЬЁЙ, А ЗАТЕМ ЗАБЕРИТЕ ФЕРЗЯ."},
    {"ВСКРЫТЫЙ ШАХ: ПРИМЕР", FEN_START,
     "6|ЧЁРНЫЕ ВЗЯЛИ ПЕШКУ, ПОВТОРЯЯ ХОДЫ БЕЛЫХ.|7|ФЕРЗЬ И ЧЁРНЫЙ КОРОЛЬ ОКАЗАЛИСЬ НА ОДНОЙ ЛИНИИ e.|"
     "8|ОШИБКА! НУЖНО БЫЛО ИГРАТЬ Фe7.|"
     "9|ВСКРЫТЫЙ ШАХ: КОНЬ УШЁЛ С ЛИНИИ e, И ФЕРЗЬ e2 ДАЛ ШАХ. А САМ КОНЬ НАПАЛ НА ФЕРЗЯ d8!|"
     "12|БЕЛЫЕ ВЫИГРАЛИ ФЕРЗЯ ЗА КОНЯ. ЭТА ЛОВУШКА ИЗВЕСТНА В РУССКОЙ ПАРТИИ.",
     LM_GAME, "e2e4 e7e5 g1f3 g8f6 f3e5 f6e4 d1e2 e4f6 e5c6 d8e7 c6e7 f8e7",
     "ВСКРЫТЫЙ ШАХ: ФИГУРА УХОДИТ С ЛИНИИ И ОТКРЫВАЕТ ШАХ ОТ ДРУГОЙ ФИГУРЫ. ТА, ЧТО УШЛА, СВОБОДНО "
     "НАПАДАЕТ НА ЧТО УГОДНО - СОПЕРНИК ЗАНЯТ ШАХОМ."},
    {"ВСКРЫТЫЙ ШАХ: ВАШ ХОД", "4k3/8/8/8/q7/8/4B3/4R1K1 w - - 0 1", "", LM_PUZZLE, "e2b5 e8f7 b5a4",
     "СЛОН ЗАКРЫВАЕТ ЛИНИЮ e. УВЕДИТЕ ЕГО С ШАХОМ ТАК, ЧТОБЫ ОН НАПАЛ НА ФЕРЗЯ, А ПОТОМ ЗАБЕРИТЕ ФЕРЗЯ."},
    {"ПОСЛЕДНЯЯ ГОРИЗОНТАЛЬ: ПРИМЕР", "2r3k1/3q1ppp/8/8/8/8/2Q2PPP/2R3K1 w - - 0 1",
     "1|ЖЕРТВА ФЕРЗЯ! ЧЁРНЫЙ ФЕРЗЬ ДОЛЖЕН ВЗЯТЬ.|2|ЕДИНСТВЕННЫЙ ЗАЩИТНИК ОТВЛЕЧЁН.|"
     "3|МАТ: КОРОЛЮ МЕШАЮТ ЕГО ЖЕ ПЕШКИ.",
     LM_GAME, "c2c8 d7c8 c1c8",
     "КОГДА КОРОЛЬ ЗАПЕРТ СВОИМИ ПЕШКАМИ, ЗАЩИТНИК ПОСЛЕДНЕЙ ГОРИЗОНТАЛИ ПЕРЕГРУЖЕН. ЕГО МОЖНО ОТВЛЕЧЬ "
     "ЖЕРТВОЙ."},
    {"ПОСЛЕДНЯЯ ГОРИЗОНТАЛЬ: ВАШ ХОД", "3r2k1/4qppp/8/8/8/8/3Q1PPP/3R2K1 w - - 0 1", "", LM_PUZZLE, "d2d8 e7d8 #",
     "ЛАДЬЮ d8 ЗАЩИЩАЕТ ФЕРЗЬ e7. ОТВЛЕКИТЕ ЕГО ЖЕРТВОЙ И ПОСТАВЬТЕ МАТ."},
    {"СПЁРТЫЙ МАТ: ПРИМЕР", FEN_START,
     "6|РИСКОВАННЫЙ ХОД: ЧЁРНЫЕ ОТДАЮТ ПЕШКУ e5.|8|ФЕРЗЬ НАПАДАЕТ НА КОНЯ И ПЕШКУ g2.|"
     "9|ЖАДНОСТЬ: КОНЬ БЕРЁТ ПЕШКУ И ВИЛКОЙ НАПАДАЕТ НА ЛАДЬЮ И ФЕРЗЯ.|"
     "13|БЕЛЫЕ ЗАКРЫЛИСЬ СЛОНОМ, НО ТЕПЕРЬ КОРОЛЬ ОКРУЖЁН СВОИМИ ФИГУРАМИ.|"
     "14|СПЁРТЫЙ МАТ! КОРОЛЮ НЕКУДА ДЕТЬСЯ ИЗ-ЗА СОБСТВЕННЫХ ФИГУР. ЭТО ЛОВУШКА БЛЭКБЕРНА.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1c4 c6d4 f3e5 d8g5 e5f7 g5g2 h1f1 g2e4 c4e2 d4f3",
     "СПЁРТЫЙ МАТ СТАВИТ ОБЫЧНО КОНЬ: КОРОЛЬ ОКРУЖЁН СВОИМИ ЖЕ ФИГУРАМИ И НЕ МОЖЕТ УЙТИ."},
    {"СПЁРТЫЙ МАТ: ВАШ ХОД", "5r1k/6pp/7N/3Q4/8/8/8/6K1 w - - 0 1", "", LM_PUZZLE, "d5g8 f8g8 #",
     "ЗНАМЕНИТАЯ КОМБИНАЦИЯ: ЖЕРТВУЙТЕ ФЕРЗЯ ТАК, ЧТОБЫ ЛАДЬЯ ЗАКРЫЛА КОРОЛЮ ПОСЛЕДНЕЕ ПОЛЕ, А ЗАТЕМ МАТ КОНЁМ."},
    {"МАТ ЛЕГАЛЯ: ПРИМЕР", FEN_START,
     "6|СЛОН СВЯЗАЛ КОНЯ f3 С ФЕРЗЁМ. КАЖЕТСЯ, КОНЮ НЕЛЬЗЯ УХОДИТЬ.|9|А БЕЛЫЕ ВСЁ РАВНО УХОДЯТ КОНЁМ!|"
     "10|ЧЁРНЫЕ ЖАДНО ЗАБРАЛИ ФЕРЗЯ...|11|ШАХ СЛОНОМ, КОРОЛЮ ОСТАЁТСЯ ОДНО ПОЛЕ.|"
     "13|МАТ ТРЕМЯ ЛЁГКИМИ ФИГУРАМИ! СВЯЗКА С ФЕРЗЁМ ОКАЗАЛАСЬ ЛОЖНОЙ.",
     LM_GAME, "e2e4 e7e5 g1f3 d7d6 f1c4 c8g4 b1c3 g7g6 f3e5 g4d1 c4f7 e8e7 c3d5",
     "СВЯЗКА С ФЕРЗЁМ НЕ АБСОЛЮТНА: ФИГУРА МОЖЕТ УЙТИ, ЕСЛИ ВЗЯТИЕ ФЕРЗЯ ОБОЙДЁТСЯ СОПЕРНИКУ ДОРОЖЕ. "
     "ЭТОЙ ЛОВУШКЕ БОЛЬШЕ 250 ЛЕТ."},
    {"МАТ ЛЕГАЛЯ: ВАШ ХОД", "rn1qkbnr/ppp2p1p/3p2p1/4N3/2B1P3/2N5/PPPP1PPP/R1BbK2R w KQkq - 0 1", "", LM_PUZZLE,
     "c4f7 e8e7 #", "ЧЁРНЫЕ ТОЛЬКО ЧТО ЗАБРАЛИ ВАШЕГО ФЕРЗЯ. НАКАЖИТЕ ИХ: ШАХ СЛОНОМ, А ЗАТЕМ МАТ КОНЁМ."},
};

// Дебюты: как начать партию. Пример (LM_GAME) + «сыграйте сами» (LM_PUZZLE).
#define FEN_AFTER_E4 "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1"
#define FEN_AFTER_D4 "rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq - 0 1"
static const LPage LP_OPEN2[] = {
    {"ПЕРВЫЙ ХОД", FEN_START, "e2>e4 d2>d4 c2>c4 g1>f3", LM_SHOW, "",
     "САМЫЕ ПОПУЛЯРНЫЕ ПЕРВЫЕ ХОДЫ:\n1.e4 - ОТКРЫТАЯ ИГРА, БЫСТРОЕ РАЗВИТИЕ И АТАКА.\n"
     "1.d4 - БОЛЕЕ СПОКОЙНЫЕ, ЗАКРЫТЫЕ ПОЗИЦИИ.\n1.c4 - АНГЛИЙСКОЕ НАЧАЛО, БОРЬБА ЗА ЦЕНТР С ФЛАНГА.\n"
     "1.Кf3 - ГИБКИЙ ХОД.\nВСЕ ОНИ ЗАНИМАЮТ ИЛИ КОНТРОЛИРУЮТ ЦЕНТР."},
    {"КАК ВЫБРАТЬ ДЕБЮТ", FEN_START, "e4:g d4:g e5:g d5:g", LM_SHOW, "",
     "ЗА БЕЛЫХ НОВИЧКУ ПОДОЙДУТ ИТАЛЬЯНСКАЯ ПАРТИЯ ИЛИ ЛОНДОНСКАЯ СИСТЕМА.\n"
     "ЗА ЧЁРНЫХ ПРОТИВ 1.e4 - ОТВЕТ 1...e5 ИЛИ ЗАЩИТА КАРО-КАНН, ПРОТИВ 1.d4 - ОТВЕТ 1...d5.\n"
     "НЕ ЗАУЧИВАЙТЕ ДЛИННЫЕ ВАРИАНТЫ: ВАЖНЕЕ ПОНЯТЬ ИДЕИ - ЦЕНТР, РАЗВИТИЕ, РОКИРОВКА.\n"
     "ДАЛЬШЕ - 12 ДЕБЮТОВ. СНАЧАЛА СМОТРИТЕ ПРИМЕР, ПОТОМ СЫГРАЙТЕ ЕГО САМИ."},

    {"ИТАЛЬЯНСКАЯ ПАРТИЯ", FEN_START,
     "1|ЗАНИМАЕМ ЦЕНТР И ОТКРЫВАЕМ ДОРОГУ ФЕРЗЮ И СЛОНУ.|3|КОНЬ РАЗВИВАЕТСЯ И НАПАДАЕТ НА e5.|"
     "4|ЧЁРНЫЕ ЗАЩИЩАЮТ ПЕШКУ КОНЁМ.|5|СЛОН НАЦЕЛЕН НА СЛАБОЕ ПОЛЕ f7.|6|ЧЁРНЫЕ ОТВЕЧАЮТ ТЕМ ЖЕ: СЛОН СМОТРИТ НА f2.|"
     "7|ГОТОВИМ ХОД d4 И БОЛЬШОЙ ЦЕНТР.|9|СПОКОЙНЫЙ ВАРИАНТ: ПЕШКА d3 НАДЁЖНО ЗАЩИЩАЕТ e4.|"
     "11|РОКИРОВКА: КОРОЛЬ В БЕЗОПАСНОСТИ, ЛАДЬЯ ВСТУПАЕТ В ИГРУ.|"
     "12|РАЗВИТИЕ ЗАВЕРШЕНО. ПЛАН БЕЛЫХ: Лe1, Кbd2-f1-g3 И НАСТУПЛЕНИЕ b4.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 c2c3 g8f6 d2d3 d7d6 e1g1 e8g8",
     "ОДИН ИЗ СТАРЕЙШИХ И САМЫХ ПОНЯТНЫХ ДЕБЮТОВ. БЕЛЫЕ БЫСТРО РАЗВИВАЮТ ФИГУРЫ И ДЕЛАЮТ РОКИРОВКУ."},
    {"СЫГРАЙТЕ: ИТАЛЬЯНСКАЯ", FEN_START, "", LM_PUZZLE, "e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 c2c3 g8f6 d2d3 d7d6 e1g1",
     "СЫГРАЙТЕ ИТАЛЬЯНСКУЮ ПАРТИЮ ЗА БЕЛЫХ ДО РОКИРОВКИ. СОПЕРНИК ОТВЕЧАЕТ САМ. ЗАБЫЛИ ХОД - НАЖМИТЕ ПОДСКАЗКА."},

    {"ИСПАНСКАЯ ПАРТИЯ", FEN_START,
     "5|СЛОН НАПАДАЕТ НА КОНЯ, КОТОРЫЙ ЗАЩИЩАЕТ e5.|6|ЧЁРНЫЕ СРАЗУ СПРАШИВАЮТ СЛОНА.|"
     "7|СЛОН ОТСТУПАЕТ, СОХРАНЯЯ ДАВЛЕНИЕ НА c6.|9|БЕЛЫЕ НЕ БОЯТСЯ ЗА e4: ПОСЛЕ Кxe4 ЛАДЬЯ НА e1 ВЕРНЁТ ПЕШКУ.|"
     "11|ЛАДЬЯ ЗАЩИЩАЕТ ПЕШКУ e4.|12|ЧЁРНЫЕ ОТГОНЯЮТ СЛОНА ПЕШКОЙ.|13|СЛОН ВСТАЛ НА ДИАГОНАЛЬ a2-g8 И ЦЕЛИТСЯ В f7.|"
     "15|ГОТОВИМ d4.|16|ГЛАВНАЯ ПОЗИЦИЯ ИСПАНСКОЙ ПАРТИИ. ДАЛЬШЕ БЕЛЫЕ ИГРАЮТ h3 И d4.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6 c2c3 e8g8",
     "ЕЁ ЕЩЁ НАЗЫВАЮТ РУЙ ЛОПЕС. ЛЮБИМЫЙ ДЕБЮТ ЧЕМПИОНОВ МИРА: БЕЛЫЕ ДОЛГО ДАВЯТ НА ЦЕНТР ЧЁРНЫХ."},
    {"СЫГРАЙТЕ: ИСПАНСКАЯ", FEN_START, "", LM_PUZZLE,
     "e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6 c2c3",
     "СЫГРАЙТЕ ИСПАНСКУЮ ПАРТИЮ ЗА БЕЛЫХ. СОПЕРНИК ОТВЕЧАЕТ САМ. ЗАБЫЛИ ХОД - НАЖМИТЕ ПОДСКАЗКА."},

    {"ШОТЛАНДСКАЯ ПАРТИЯ", FEN_START,
     "5|СРАЗУ БЬЁМ В ЦЕНТР, НЕ ДАВАЯ ЧЁРНЫМ ВРЕМЕНИ.|7|БЕЛЫЕ ВЕРНУЛИ ПЕШКУ. КОНЬ СТОИТ В ЦЕНТРЕ.|"
     "8|СЛОН НАПАДАЕТ НА КОНЯ d4.|9|СЛОН ЗАЩИЩАЕТ КОНЯ.|10|ФЕРЗЬ ТОЖЕ НАПАДАЕТ НА d4.|"
     "11|ПЕШКА c3 НАДЁЖНО УКРЕПЛЯЕТ КОНЯ.|13|СЛОН ВЫХОДИТ НА АКТИВНУЮ ДИАГОНАЛЬ. БЕЛЫЕ ГОТОВЫ К РОКИРОВКЕ.",
     LM_GAME, "e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 f8c5 c1e3 d8f6 c2c3 g8e7 f1c4",
     "ПРЯМОЛИНЕЙНЫЙ ДЕБЮТ: БЕЛЫЕ СРАЗУ ВСКРЫВАЮТ ЦЕНТР И ПОЛУЧАЮТ СВОБОДНУЮ ИГРУ."},
    {"СЫГРАЙТЕ: ШОТЛАНДСКАЯ", FEN_START, "", LM_PUZZLE, "e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 f8c5 c1e3 d8f6 c2c3 g8e7 f1c4",
     "СЫГРАЙТЕ ШОТЛАНДСКУЮ ПАРТИЮ ЗА БЕЛЫХ. СОПЕРНИК ОТВЕЧАЕТ САМ."},

    {"ЛОНДОНСКАЯ СИСТЕМА", FEN_START,
     "3|СЛОН ВЫХОДИТ ДО ХОДА e3, ЧТОБЫ НЕ ЗАПЕРЕТЬ ЕГО ПЕШКОЙ.|5|ПЕШКИ c3, d4, e3 ОБРАЗУЮТ ПРОЧНУЮ ПИРАМИДУ.|"
     "8|ЧЁРНЫЕ АТАКУЮТ ЦЕНТР С ФЛАНГА.|9|ПЕШКА c3 ЗАЩИЩАЕТ d4.|11|КОНЬ ИДЁТ НА d2: ПОЛЕ c3 ЗАНЯТО ПЕШКОЙ.|"
     "12|ЧЁРНЫЕ ПРЕДЛАГАЮТ РАЗМЕН СЛОНОВ.|13|СЛОН ОТХОДИТ И СОХРАНЯЕТСЯ. ПЛАН БЕЛЫХ: Сd3, 0-0, Кe5.",
     LM_GAME, "d2d4 d7d5 c1f4 g8f6 e2e3 e7e6 g1f3 c7c5 c2c3 b8c6 b1d2 f8d6 f4g3",
     "СИСТЕМА, А НЕ ДЕБЮТ: БЕЛЫЕ СТРОЯТ ОДНУ И ТУ ЖЕ НАДЁЖНУЮ РАССТАНОВКУ ПОЧТИ ПРОТИВ ЛЮБОЙ ИГРЫ ЧЁРНЫХ. "
     "ОТЛИЧНЫЙ ВЫБОР ДЛЯ НАЧИНАЮЩИХ."},
    {"СЫГРАЙТЕ: ЛОНДОНСКАЯ", FEN_START, "", LM_PUZZLE, "d2d4 d7d5 c1f4 g8f6 e2e3 e7e6 g1f3 c7c5 c2c3 b8c6 b1d2 f8d6 f4g3",
     "ПОСТРОЙТЕ ЛОНДОНСКУЮ СИСТЕМУ ЗА БЕЛЫХ. СОПЕРНИК ОТВЕЧАЕТ САМ."},

    {"ФЕРЗЕВЫЙ ГАМБИТ", FEN_START,
     "3|ГАМБИТ: БЕЛЫЕ ПРЕДЛАГАЮТ ПЕШКУ, ЧТОБЫ ОТВЛЕЧЬ ПЕШКУ d5 ОТ ЦЕНТРА.|"
     "4|ОТКАЗАННЫЙ ГАМБИТ: ЧЁРНЫЕ НАДЁЖНО ДЕРЖАТ d5.|6|КОНЬ ЕЩЁ РАЗ ЗАЩИЩАЕТ d5.|"
     "7|СВЯЗКА: КОНЯ f6 НЕЛЬЗЯ УБРАТЬ, ИНАЧЕ ПОГИБНЕТ ФЕРЗЬ.|8|ЧЁРНЫЕ СНИМАЮТ СВЯЗКУ.|"
     "11|КЛАССИЧЕСКАЯ ПОЗИЦИЯ: ВСЕ ФИГУРЫ БЕЛЫХ СМОТРЯТ В ЦЕНТР.",
     LM_GAME, "d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8 g1f3",
     "ГЛАВНЫЙ ДЕБЮТ ПОСЛЕ 1.d4. ЕСЛИ ЧЁРНЫЕ ВОЗЬМУТ c4, БЕЛЫЕ ЛЕГКО ВЕРНУТ ПЕШКУ И ЗАХВАТЯТ ЦЕНТР."},
    {"СЫГРАЙТЕ: ФЕРЗЕВЫЙ ГАМБИТ", FEN_START, "", LM_PUZZLE, "d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8 g1f3",
     "СЫГРАЙТЕ ФЕРЗЕВЫЙ ГАМБИТ ЗА БЕЛЫХ. СОПЕРНИК ОТВЕЧАЕТ САМ."},

    {"АНГЛИЙСКОЕ НАЧАЛО", FEN_START,
     "1|БЕЛЫЕ КОНТРОЛИРУЮТ ПОЛЕ d5 ФЛАНГОВОЙ ПЕШКОЙ.|5|БЕЛЫЕ ГОТОВЯТ СЛОНА НА g2.|6|ЧЁРНЫЕ ЗАНИМАЮТ ЦЕНТР.|"
     "9|СЛОН g2 ДАВИТ ПО ДЛИННОЙ ДИАГОНАЛИ.|10|КОНЬ ОТСТУПАЕТ ИЗ-ПОД УДАРА.|"
     "13|ЭТО ПОХОЖЕ НА СИЦИЛИАНСКУЮ ЗАЩИТУ, НО С ЛИШНИМ ТЕМПОМ ДЛЯ БЕЛЫХ.",
     LM_GAME, "c2c4 e7e5 b1c3 g8f6 g2g3 d7d5 c4d5 f6d5 f1g2 d5b6 g1f3 b8c6 e1g1",
     "СПОКОЙНЫЙ ПОЗИЦИОННЫЙ ДЕБЮТ: БЕЛЫЕ БОРЮТСЯ ЗА ЦЕНТР ИЗДАЛЕКА, ФИГУРАМИ."},
    {"СЫГРАЙТЕ: АНГЛИЙСКОЕ", FEN_START, "", LM_PUZZLE, "c2c4 e7e5 b1c3 g8f6 g2g3 d7d5 c4d5 f6d5 f1g2 d5b6 g1f3 b8c6 e1g1",
     "СЫГРАЙТЕ АНГЛИЙСКОЕ НАЧАЛО ЗА БЕЛЫХ. СОПЕРНИК ОТВЕЧАЕТ САМ."},

    {"РУССКАЯ ПАРТИЯ", FEN_START,
     "4|ЧЁРНЫЕ НЕ ЗАЩИЩАЮТ e5, А САМИ НАПАДАЮТ НА e4.|5|БЕЛЫЕ ВЗЯЛИ ПЕШКУ.|"
     "6|ВАЖНО! СНАЧАЛА ПРОГОНЯЕМ КОНЯ. СРАЗУ 3...Кxe4? ПЛОХО ИЗ-ЗА 4.Фe2.|8|ТЕПЕРЬ ЧЁРНЫЕ ВЕРНУЛИ ПЕШКУ.|"
     "10|ЧЁРНЫЕ УКРЕПЛЯЮТ КОНЯ В ЦЕНТРЕ.|12|РАВНАЯ НАДЁЖНАЯ ПОЗИЦИЯ: ЧЁРНЫЕ ГОТОВЫ К РОКИРОВКЕ.",
     LM_GAME, "e2e4 e7e5 g1f3 g8f6 f3e5 d7d6 e5f3 f6e4 d2d4 d6d5 f1d3 f8d6",
     "ЗАЩИТА ПЕТРОВА - НАДЁЖНЫЙ ОТВЕТ ЧЁРНЫХ НА 1.e4. ЕЁ ПРИДУМАЛИ РУССКИЕ ШАХМАТИСТЫ В 19 ВЕКЕ."},
    {"СЫГРАЙТЕ: РУССКАЯ", FEN_AFTER_E4, "", LM_PUZZLE, "e7e5 g1f3 g8f6 f3e5 d7d6 e5f3 f6e4 d2d4 d6d5 f1d3 f8d6",
     "ТЕПЕРЬ ВЫ ИГРАЕТЕ ЧЁРНЫМИ. БЕЛЫЕ СЫГРАЛИ 1.e4. ПОСТРОЙТЕ РУССКУЮ ПАРТИЮ."},

    {"СИЦИЛИАНСКАЯ ЗАЩИТА", FEN_START,
     "2|САМЫЙ ПОПУЛЯРНЫЙ ОТВЕТ НА 1.e4: ЧЁРНЫЕ БОРЮТСЯ ЗА ПОЛЕ d4 ФЛАНГОВОЙ ПЕШКОЙ.|5|БЕЛЫЕ ВСКРЫВАЮТ ЦЕНТР.|"
     "6|ЧЁРНЫЕ ОТДАЮТ ФЛАНГОВУЮ ПЕШКУ c ЗА ЦЕНТРАЛЬНУЮ d. ЭТО ВЫГОДНЫЙ ОБМЕН.|"
     "8|КОНЬ РАЗВИВАЕТСЯ С НАПАДЕНИЕМ НА e4.|"
     "10|ВАРИАНТ НАЙДОРФА: a6 ГОТОВИТ b5. ЛЮБИМЫЙ ВАРИАНТ ФИШЕРА И КАСПАРОВА.",
     LM_GAME, "e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6",
     "ОСТРАЯ ЗАЩИТА ДЛЯ ТЕХ, КТО ИГРАЕТ НА ВЫИГРЫШ ЧЁРНЫМИ. ПОЗИЦИЯ НЕСИММЕТРИЧНАЯ, ИГРА НА ОБОИХ ФЛАНГАХ."},
    {"СЫГРАЙТЕ: СИЦИЛИАНСКАЯ", FEN_AFTER_E4, "", LM_PUZZLE, "c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6",
     "ВЫ ИГРАЕТЕ ЧЁРНЫМИ. БЕЛЫЕ СЫГРАЛИ 1.e4. СЫГРАЙТЕ СИЦИЛИАНСКУЮ ЗАЩИТУ."},

    {"ФРАНЦУЗСКАЯ ЗАЩИТА", FEN_START,
     "2|СКРОМНЫЙ ХОД, НО ОН ГОТОВИТ d5.|4|ЧЁРНЫЕ ОСПАРИВАЮТ ЦЕНТР.|5|БЕЛЫЕ ЗАХВАТЫВАЮТ ПРОСТРАНСТВО.|"
     "6|ГЛАВНАЯ ИДЕЯ: ПОДРЫВАТЬ ПЕШЕЧНУЮ ЦЕПЬ БЕЛЫХ У ОСНОВАНИЯ - НА d4.|8|ЕЩЁ ОДНА ФИГУРА БЬЁТ ПО d4.|"
     "10|ФЕРЗЬ НАПАДАЕТ НА d4 И b2. ЦЕНТР БЕЛЫХ ПОД ДАВЛЕНИЕМ.",
     LM_GAME, "e2e4 e7e6 d2d4 d7d5 e4e5 c7c5 c2c3 b8c6 g1f3 d8b6",
     "ПРОЧНАЯ ЗАЩИТА: ЧЁРНЫЕ УСТУПАЮТ ПРОСТРАНСТВО, НО ПОТОМ АТАКУЮТ ЦЕНТР БЕЛЫХ. МИНУС - СЛОН c8 "
     "ЗАПЕРТ ПЕШКОЙ e6."},
    {"СЫГРАЙТЕ: ФРАНЦУЗСКАЯ", FEN_AFTER_E4, "", LM_PUZZLE, "e7e6 d2d4 d7d5 e4e5 c7c5 c2c3 b8c6 g1f3 d8b6",
     "ВЫ ИГРАЕТЕ ЧЁРНЫМИ. СЫГРАЙТЕ ФРАНЦУЗСКУЮ ЗАЩИТУ."},

    {"ЗАЩИТА КАРО-КАНН", FEN_START,
     "2|ГОТОВИМ d5, А ПУТЬ ДЛЯ СЛОНА c8 ОСТАЁТСЯ ОТКРЫТЫМ.|4|ЧЁРНЫЕ НАПАДАЮТ НА e4.|6|РАЗМЕН В ЦЕНТРЕ.|"
     "8|СЛОН ВЫХОДИТ С ТЕМПОМ - НАПАДАЕТ НА КОНЯ.|10|СЛОН ОТСТУПАЕТ, НО ОСТАЁТСЯ АКТИВНЫМ. ПОЗИЦИЯ БЕЗ СЛАБОСТЕЙ.",
     LM_GAME, "e2e4 c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5 e4g3 f5g6",
     "НАДЁЖНАЯ ЗАЩИТА: ЧЁРНЫЕ ПОЛУЧАЮТ ПРОЧНУЮ ПОЗИЦИЮ И АКТИВНОГО СЛОНА. ХОРОШИЙ ВЫБОР ДЛЯ НАЧИНАЮЩИХ."},
    {"СЫГРАЙТЕ: КАРО-КАНН", FEN_AFTER_E4, "", LM_PUZZLE, "c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5 e4g3 f5g6",
     "ВЫ ИГРАЕТЕ ЧЁРНЫМИ. СЫГРАЙТЕ ЗАЩИТУ КАРО-КАНН."},

    {"СЛАВЯНСКАЯ ЗАЩИТА", FEN_START,
     "4|ЧЁРНЫЕ ЗАЩИЩАЮТ d5 ПЕШКОЙ И НЕ ЗАПИРАЮТ СЛОНА c8.|8|ЧЁРНЫЕ ВЗЯЛИ ПЕШКУ И ХОТЯТ УДЕРЖАТЬ ЕЁ ХОДОМ b5.|"
     "9|БЕЛЫЕ МЕШАЮТ ХОДУ b5.|10|СЛОН ВЫХОДИТ НАРУЖУ ДО ХОДА e6. ЧЁРНЫЕ ОТЛИЧНО РАЗВИТЫ.",
     LM_GAME, "d2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 d5c4 a2a4 c8f5",
     "ПРОЧНЫЙ ОТВЕТ НА ФЕРЗЕВЫЙ ГАМБИТ. ЧЁРНЫЕ ДЕРЖАТ ЦЕНТР И ВЫВОДЯТ ВСЕ ФИГУРЫ."},
    {"СЫГРАЙТЕ: СЛАВЯНСКАЯ", FEN_AFTER_D4, "", LM_PUZZLE, "d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 d5c4 a2a4 c8f5",
     "ВЫ ИГРАЕТЕ ЧЁРНЫМИ. БЕЛЫЕ СЫГРАЛИ 1.d4. СЫГРАЙТЕ СЛАВЯНСКУЮ ЗАЩИТУ."},

    {"СТАРОИНДИЙСКАЯ ЗАЩИТА", FEN_START,
     "4|ЧЁРНЫЕ ГОТОВЯТ ФИАНКЕТТО - СЛОНА НА g7.|6|СЛОН g7 БЬЁТ ПО ВСЕЙ ДЛИННОЙ ДИАГОНАЛИ.|"
     "7|БЕЛЫЕ СТРОЯТ БОЛЬШОЙ ЦЕНТР. ЧЁРНЫЕ ПОКА ЭТО ДОПУСКАЮТ...|10|КОРОЛЬ НАДЁЖНО СПРЯТАН ЗА СЛОНОМ.|"
     "12|...А ТЕПЕРЬ БЬЮТ ПО ЦЕНТРУ. ДАЛЬШЕ ЧЁРНЫЕ ЧАСТО АТАКУЮТ НА КОРОЛЕВСКОМ ФЛАНГЕ.",
     LM_GAME, "d2d4 g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8 f1e2 e7e5",
     "АТАКУЮЩАЯ ЗАЩИТА: ЧЁРНЫЕ ОТДАЮТ ЦЕНТР, ЧТОБЫ ПОТОМ ЕГО ПОДОРВАТЬ. ДЛЯ ЛЮБИТЕЛЕЙ ОСТРОЙ ИГРЫ."},
    {"СЫГРАЙТЕ: СТАРОИНДИЙСКАЯ", FEN_AFTER_D4, "", LM_PUZZLE, "g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8 f1e2 e7e5",
     "ВЫ ИГРАЕТЕ ЧЁРНЫМИ. СЫГРАЙТЕ СТАРОИНДИЙСКУЮ ЗАЩИТУ."},
};

#define LCH(t, s, a) {t, s, a, (int)(sizeof(a) / sizeof(a[0]))}
static const LChapter CHAPTERS[] = {
    LCH("ОСНОВЫ", "ДОСКА, РАССТАНОВКА, ЦЕЛЬ", LP_BASICS),
    LCH("КАК ХОДЯТ ФИГУРЫ", "ПОПРОБУЙТЕ САМИ НА ДОСКЕ", LP_PIECES),
    LCH("ОСОБЫЕ ХОДЫ", "РОКИРОВКА, ВЗЯТИЕ НА ПРОХОДЕ", LP_SPECIAL),
    LCH("ШАХ, МАТ И НИЧЬЯ", "КАК ЗАКАНЧИВАЕТСЯ ПАРТИЯ", LP_ENDING),
    LCH("ЦЕННОСТЬ ФИГУР", "ЧТО НА ЧТО МЕНЯТЬ", LP_VALUE),
    LCH("ДЕБЮТ", "КАК НАЧИНАТЬ ПАРТИЮ", LP_OPENING),
    LCH("ТАКТИКА", "ВИЛКА, СВЯЗКА, ЗАДАЧИ", LP_TACTICS),
    LCH("ЭНДШПИЛЬ", "КАК ДОВЕСТИ ДЕЛО ДО МАТА", LP_ENDGAME),
    LCH("СТРАТЕГИЯ", "ПЛАН И ПОЛЕЗНЫЕ СОВЕТЫ", LP_STRATEGY),
    LCH("ЗАПИСЬ ХОДОВ", "КАК ЧИТАТЬ СПИСОК ХОДОВ", LP_NOTATION),
    LCH("ТАКТИКА НА ПРИМЕРАХ", "ПАРТИИ И ЗАДАЧИ НА ПРИЁМЫ", LP_TACT2),
    LCH("ДЕБЮТЫ: КАК НАЧАТЬ", "12 ДЕБЮТОВ, ПРИМЕРЫ И ПРАКТИКА", LP_OPEN2),
};
static const int NCHAP = (int)(sizeof(CHAPTERS) / sizeof(CHAPTERS[0]));

struct LMark {
    int kind;  // 0 — подсветка, 1 — стрелка
    int a, b;
    char c;
};
static int gLCh = 0, gLPg = 0;
static eng::Board gLB;
static bool gLWB = true;
static int gLSel = -1;
static std::vector<eng::Move> gLTargets;
static int gLStatus = 0;  // 0 — думаем, 1 — верно, 2 — неверно
static int gLTries = 0;
static Uint32 gLResetAt = 0;
static eng::Move gLHint = 0;
static bool gLShowHint = false;
static int gLLastFrom = -1, gLLastTo = -1;
static std::vector<LMark> gLMarks;
// пример партии
static std::vector<eng::Board> gLGPos;
static std::vector<eng::Move> gLGMoves;
static std::vector<std::string> gLGSan;
static std::vector<std::pair<int, std::string>> gLGNotes;
static int gLGPly = 0;
static bool gLGAuto = false;
static Uint32 gLGNext = 0;
// задача в несколько ходов
static std::vector<std::string> gLTok;
static int gLStep = 0;
static Uint32 gLReplyAt = 0;
static eng::Board gLSaved;  // позиция до неверного хода — к ней откатываемся
static int gLSavedFrom = -1, gLSavedTo = -1;

static int parseSq(const char *s) {
    if (s[0] < 'a' || s[0] > 'h' || s[1] < '1' || s[1] > '8') return -1;
    return (s[1] - '1') * 8 + (s[0] - 'a');
}
static const LPage &curPage() { return CHAPTERS[gLCh].pages[gLPg]; }
static int puzzlesIn(int ch) {
    int n = 0;
    for (int i = 0; i < CHAPTERS[ch].n; i++)
        if (CHAPTERS[ch].pages[i].mode == LM_PUZZLE) n++;
    return n;
}
static int solvedIn(int ch) {
    int n = 0;
    for (int i = 0; i < CHAPTERS[ch].n; i++)
        if (CHAPTERS[ch].pages[i].mode == LM_PUZZLE && (gSolved[ch] >> i & 1)) n++;
    return n;
}

static bool isMateMove(eng::Board b, eng::Move m) {
    eng::Undo u;
    b.make(m, u);
    if (!b.inCheck(b.side)) return false;
    eng::MoveList ml;
    b.genLegal(ml);
    return ml.n == 0;
}
static bool puzzleOk(eng::Board &b, eng::Move m, const char *sol) {
    if (strcmp(sol, "#") == 0) return isMateMove(b, m);
    return eng::toUCI(m).compare(0, 4, std::string(sol).substr(0, 4)) == 0;
}
static std::vector<std::string> splitWords(const char *s) {
    std::vector<std::string> v;
    std::string cur;
    for (const char *p = s;; p++) {
        if (*p == ' ' || !*p) {
            if (!cur.empty()) v.push_back(cur);
            cur.clear();
            if (!*p) break;
        } else {
            cur += *p;
        }
    }
    return v;
}
static eng::Move findUci(eng::Board &b, const std::string &u) {
    eng::MoveList ml;
    b.genLegal(ml);
    for (int i = 0; i < ml.n; i++)
        if (eng::toUCI(ml.m[i]) == u) return ml.m[i];
    return 0;
}
static void computeHint() {
    gLHint = 0;
    if (gLStep >= (int)gLTok.size()) return;
    eng::MoveList ml;
    gLB.genLegal(ml);
    for (int i = 0; i < ml.n; i++)
        if (puzzleOk(gLB, ml.m[i], gLTok[(size_t)gLStep].c_str())) {
            gLHint = ml.m[i];
            return;
        }
}
static void lessonGameShow(int ply) {
    int n = (int)gLGMoves.size();
    gLGPly = std::max(0, std::min(n, ply));
    gLB = gLGPos[(size_t)gLGPly];
    if (gLGPly > 0) {
        gLLastFrom = eng::mFrom(gLGMoves[(size_t)gLGPly - 1]);
        gLLastTo = eng::mTo(gLGMoves[(size_t)gLGPly - 1]);
    } else {
        gLLastFrom = gLLastTo = -1;
    }
}

static void lessonTargets() {
    gLTargets.clear();
    if (gLSel < 0) return;
    eng::MoveList ml;
    gLB.genLegal(ml);
    for (int i = 0; i < ml.n; i++)
        if (eng::mFrom(ml.m[i]) == gLSel) gLTargets.push_back(ml.m[i]);
}

static void loadLessonPage(bool fresh) {
    const LPage &p = curPage();
    gLB.setFEN(p.fen);
    gLWB = !(p.mode == LM_PUZZLE && gLB.side == eng::BLACK);
    gLSel = -1;
    gLTargets.clear();
    gLStatus = 0;
    gLResetAt = 0;
    gLLastFrom = gLLastTo = -1;
    if (fresh) {
        gLTries = 0;
        gLShowHint = false;
    }
    gLMarks.clear();
    gLReplyAt = 0;
    gLGAuto = false;
    const char *s = p.mode == LM_GAME ? "" : p.marks;
    while (*s) {
        while (*s == ' ') s++;
        if (!*s) break;
        int a = parseSq(s);
        if (a >= 0 && s[2] == ':' && s[3]) {
            LMark m;
            m.kind = 0; m.a = a; m.b = -1; m.c = s[3];
            gLMarks.push_back(m);
            s += 4;
        } else if (a >= 0 && s[2] == '>' && parseSq(s + 3) >= 0) {
            LMark m;
            m.kind = 1; m.a = a; m.b = parseSq(s + 3); m.c = 'g';
            gLMarks.push_back(m);
            s += 5;
        } else {
            while (*s && *s != ' ') s++;
        }
    }
    if (p.mode == LM_MOVES) {
        gLSel = parseSq(p.sol);
        lessonTargets();
    }
    gLHint = 0;
    if (p.mode == LM_PUZZLE) {
        gLTok = splitWords(p.sol);
        gLStep = 0;
        computeHint();
    }
    if (p.mode == LM_GAME) {
        gLGPos.assign(1, gLB);
        gLGMoves.clear();
        gLGSan.clear();
        for (auto &u : splitWords(p.sol)) {
            eng::Board b = gLGPos.back();
            eng::Move m = findUci(b, u);
            if (!m) break;
            gLGSan.push_back(eng::toSAN(b, m));
            eng::Undo un;
            b.make(m, un);
            gLGMoves.push_back(m);
            gLGPos.push_back(b);
        }
        gLGNotes.clear();
        auto parts = std::string(p.marks);
        size_t i = 0;
        while (i < parts.size()) {
            size_t a = parts.find('|', i);
            if (a == std::string::npos) break;
            size_t b2 = parts.find('|', a + 1);
            if (b2 == std::string::npos) b2 = parts.size();
            gLGNotes.push_back({atoi(parts.substr(i, a - i).c_str()), parts.substr(a + 1, b2 - a - 1)});
            i = b2 + 1;
        }
        lessonGameShow(0);
    }
}

static void openLesson(int ch, int pg) {
    gLCh = std::max(0, std::min(NCHAP - 1, ch));
    gLPg = std::max(0, std::min(CHAPTERS[gLCh].n - 1, pg));
    loadLessonPage(true);
}

static void lessonMove(eng::Move m) {
    const LPage &p = curPage();
    int from = eng::mFrom(m), to = eng::mTo(m);
    bool cap = (eng::mFlags(m) & eng::F_CAP) != 0;
    if (p.mode == LM_MOVES) {
        int c = gLB.side;
        eng::Undo u;
        gLB.make(m, u);
        gLB.side = c;  // ходит всё время одна сторона — это «песочница»
        gLB.ep = -1;
        gLB.hash = gLB.computeHash();
        gLLastFrom = from;
        gLLastTo = to;
        gLSel = to;
        lessonTargets();
        playSound(cap ? SND_CAPTURE : SND_MOVE);
        return;
    }
    bool ok = gLStep < (int)gLTok.size() && puzzleOk(gLB, m, gLTok[(size_t)gLStep].c_str());
    gLSaved = gLB;
    gLSavedFrom = gLLastFrom;
    gLSavedTo = gLLastTo;
    eng::Undo u;
    gLB.make(m, u);
    gLLastFrom = from;
    gLLastTo = to;
    gLSel = -1;
    gLTargets.clear();
    if (ok && gLStep + 1 < (int)gLTok.size()) {
        // верный ход, но комбинация не закончена — соперник отвечает
        gLStatus = 3;
        gLShowHint = false;
        gLReplyAt = SDL_GetTicks() + 700;
        playSound(cap ? SND_CAPTURE : SND_MOVE);
        return;
    }
    if (ok) {
        gLStatus = 1;
        gLShowHint = false;
        gSolved[gLCh] |= 1 << gLPg;
        playSound(SND_END);
        saveAll();
    } else {
        gLStatus = 2;
        gLTries++;
        if (gLTries >= 2) gLShowHint = true;
        gLResetAt = SDL_GetTicks() + 1100;
        playSound(SND_CHECK);
    }
}

// после неверного хода возвращаем только последний ход, а не всю задачу
static void lessonUndoWrong() {
    gLResetAt = 0;
    if (curPage().mode != LM_PUZZLE) {
        loadLessonPage(false);
        return;
    }
    gLB = gLSaved;
    gLLastFrom = gLSavedFrom;
    gLLastTo = gLSavedTo;
    gLStatus = 0;
    gLSel = -1;
    gLTargets.clear();
    computeHint();
}

static void lessonReply() {
    gLReplyAt = 0;
    if (gLStep + 1 >= (int)gLTok.size()) return;
    eng::Move r = findUci(gLB, gLTok[(size_t)gLStep + 1]);
    if (r) {
        bool cap = (eng::mFlags(r) & eng::F_CAP) != 0;
        gLLastFrom = eng::mFrom(r);
        gLLastTo = eng::mTo(r);
        eng::Undo u;
        gLB.make(r, u);
        playSound(gLB.inCheck(gLB.side) ? SND_CHECK : (cap ? SND_CAPTURE : SND_MOVE));
    }
    gLStep += 2;
    gLStatus = 0;
    computeHint();
}

static void lessonTap(int sq) {
    const LPage &p = curPage();
    if (p.mode == LM_GAME) {  // нажатие на доску в примере — следующий ход
        gLGAuto = false;
        if (gLGPly < (int)gLGMoves.size()) {
            lessonGameShow(gLGPly + 1);
            playSound(SND_MOVE);
        }
        return;
    }
    if (p.mode == LM_SHOW || gLStatus == 1 || gLStatus == 3 || gLResetAt || gLReplyAt) return;
    if (gLSel >= 0) {
        eng::Move pick = 0;
        for (auto m : gLTargets)
            if (eng::mTo(m) == sq && (!pick || eng::mPromo(m) == eng::QUEEN)) pick = m;
        if (pick) {
            lessonMove(pick);
            return;
        }
    }
    int pc = gLB.sq[sq];
    if (pc && eng::pColor(pc) == gLB.side) {
        gLSel = (gLSel == sq && p.mode == LM_PUZZLE) ? -1 : sq;
        lessonTargets();
        playSound(SND_CLICK);
        return;
    }
    if (p.mode == LM_PUZZLE) {
        gLSel = -1;
        gLTargets.clear();
    }
}

// =====================================================================
//                     СЕТЬ: ПРОТОКОЛ ПАРТИИ
// =====================================================================
// Строки текста: HELLO, START <цвет хозяина> <мс>, MOVE <номер> <ход> <мс>,
// RESIGN, TIMEOUT, OFFER DRAW|NEW, ACCEPT DRAW|NEW, DECLINE, BYE, PING.
enum { NU_MENU, NU_WAIT, NU_JOIN, NU_KEYPAD, NU_CONNECTING };
static int gNetUI = NU_MENU;
static std::string gNetMsg;
static std::string gNetIpInput;

static void startNetMatch(int myColor, int clockMs) {
    cancelBot();
    cancelReview();
    if (!gHaveBackup && gM.mode != MODE_NET) {
        gBackup = gM;
        gHaveBackup = true;
    }
    gM.active = true;
    gM.mode = MODE_NET;
    gM.human = myColor;
    gM.level = 1;
    gM.clockInit = std::max(0, clockMs);
    gM.tLeft[0] = gM.tLeft[1] = gM.clockInit;
    gM.flip = false;
    gM.recorded = false;
    gM.g.reset();
    gViewSide = eng::WHITE;
    clearSel();
    gAnims.clear();
    gResultPending = false;
    gOverlay = OV_NONE;
    gConfirm = CF_NONE;
    gListScroll = 0;
    gViewPly = -1;
    clearUserMarks();
    gScreen = SC_GAME;
    gLastTick = SDL_GetTicks();
    playSound(SND_CLICK);
    toast(myColor == eng::WHITE ? "ВЫ ИГРАЕТЕ БЕЛЫМИ" : "ВЫ ИГРАЕТЕ ЧЁРНЫМИ");
}

// Выход из сетевой игры: закрыть соединение и вернуть отложенную партию
static void netLeave(bool sendBye) {
    if (sendBye && gNet.state == NS_CONNECTED) {
        netSendLine("BYE");
        netFlush();
    }
    netCloseAll();
    if (gM.mode == MODE_NET) {
        if (gHaveBackup) gM = gBackup;
        else gM = Match();
        gHaveBackup = false;
        gViewSide = gM.g.cur.side;
        gOverlay = OV_NONE;
        gConfirm = CF_NONE;
        clearSel();
        gAnims.clear();
        gResultPending = false;
    }
}

static void netOffer(const char *what) {
    if (!netConnected()) {
        toast("НЕТ СВЯЗИ С СОПЕРНИКОМ");
        return;
    }
    netSendLine(std::string("OFFER ") + what);
    toast("ПРЕДЛОЖЕНИЕ ОТПРАВЛЕНО");
}

static void netHandleLine(const std::string &l) {
    char cmd[32] = {0}, arg[32] = {0};
    if (sscanf(l.c_str(), "%31s %31s", cmd, arg) < 1) return;
    std::string c = cmd, a = arg;
    if (c == "PING") return;
    if (c == "HELLO") {
        if (!gNet.isHost || gM.mode == MODE_NET) return;
        int hc = gSet.color == 2 ? (int)((SDL_GetPerformanceCounter() >> 3) & 1) : gSet.color;
        static const int MIN[4] = {0, 5, 10, 15};
        int ms = MIN[gSet.clock] * 60000;
        netSendLine("START " + std::to_string(hc) + " " + std::to_string(ms));
        startNetMatch(hc, ms);
        return;
    }
    if (c == "START") {
        if (gNet.isHost) return;
        int hc = 0, ms = 0;
        sscanf(l.c_str() + 5, "%d %d", &hc, &ms);
        startNetMatch(hc == eng::WHITE ? eng::BLACK : eng::WHITE, ms);
        return;
    }
    if (gM.mode != MODE_NET) return;
    int opp = gM.human ^ 1;
    if (c == "MOVE") {
        int ply = -1;
        char u[16] = {0};
        long long ms = 0;
        if (sscanf(l.c_str() + 4, "%d %15s %lld", &ply, u, &ms) < 2) return;
        if (gM.g.result != RES_NONE || ply != (int)gM.g.moves.size() || gM.g.cur.side != opp) {
            toast("ОШИБКА СИНХРОНИЗАЦИИ");
            return;
        }
        eng::MoveList ml;
        gM.g.cur.genLegal(ml);
        for (int i = 0; i < ml.n; i++)
            if (eng::toUCI(ml.m[i]) == u) {
                if (gM.clockInit > 0) gM.tLeft[opp] = std::max(0LL, ms);
                if (gOverlay == OV_PROMO) gOverlay = OV_NONE;
                playMove(ml.m[i], true);
                return;
            }
        toast("ОШИБКА СИНХРОНИЗАЦИИ");
        return;
    }
    if (c == "RESIGN") {
        if (gM.g.result == RES_NONE) {
            gM.g.result = opp == eng::WHITE ? RES_BLACK : RES_WHITE;
            gM.g.reason = R_RESIGN;
            gM.g.loser = opp;
            onGameEnd();
        }
        return;
    }
    if (c == "TIMEOUT") {
        if (gM.g.result == RES_NONE) onTimeout(opp);
        return;
    }
    if (c == "OFFER") {
        if (a == "DRAW" && gM.g.result != RES_NONE) return;
        gConfirm = a == "DRAW" ? CF_NET_DRAW : CF_NET_NEW;
        gOverlay = OV_CONFIRM;
        clearSel();
        playSound(SND_CHECK);
        return;
    }
    if (c == "ACCEPT") {
        if (a == "DRAW") {
            if (gM.g.result == RES_NONE) {
                gM.g.result = RES_DRAW;
                gM.g.reason = R_AGREE;
                onGameEnd();
            }
        } else if (a == "NEW") {
            startNetMatch(gM.human ^ 1, gM.clockInit);
        }
        return;
    }
    if (c == "DECLINE") {
        toast("СОПЕРНИК ОТКАЗАЛСЯ");
        return;
    }
    if (c == "BYE") {
        netCloseAll();
        if (gM.g.result == RES_NONE) {
            gM.g.result = gM.human == eng::WHITE ? RES_WHITE : RES_BLACK;
            gM.g.reason = R_LEFT;
            gM.g.loser = opp;
            onGameEnd();
        } else {
            toast("СОПЕРНИК ВЫШЕЛ ИЗ ИГРЫ");
        }
        if (gOverlay == OV_CONFIRM) {
            gOverlay = OV_NONE;
            gConfirm = CF_NONE;
        }
    }
}

static void netPoll() {
    bool wasConnecting = gNet.state == NS_CONNECTING;
    netPollIO();
    if (wasConnecting && gNet.state == NS_IDLE) {
        gNetUI = NU_JOIN;
        gNetMsg = "НЕ УДАЛОСЬ ПОДКЛЮЧИТЬСЯ";
        netScanStart();
    }
    if (gNet.lost && gNet.state == NS_CONNECTED) {
        netCloseAll();
        if (gM.mode == MODE_NET && gScreen == SC_GAME) {
            if (gM.g.result == RES_NONE) {
                gConfirm = CF_NET_LOST;
                gOverlay = OV_CONFIRM;
                clearSel();
            } else {
                toast("СОПЕРНИК ОТКЛЮЧИЛСЯ");
            }
        } else if (gScreen == SC_NET) {
            gNetUI = NU_MENU;
            gNetMsg = "СВЯЗЬ ПОТЕРЯНА";
        }
    }
}

static std::string foundLabel(const FoundGame &f) {
    std::string s = f.ip + " · ВЫ ";
    s += f.color == 0 ? "ЧЁРНЫЕ" : f.color == 1 ? "БЕЛЫЕ" : "СЛУЧАЙНО";
    if (f.clockMin > 0) s += " · " + std::to_string(f.clockMin) + " МИН";
    return s;
}

static bool netBusy() { return gNet.state != NS_IDLE || gNet.scan != SOCK_BAD; }

// =====================================================================
//                     РАЗБОР ПАРТИИ (АНАЛИЗ ОШИБОК)
// =====================================================================
// Движок оценивает каждую позицию партии. Потеря «шансов на победу» после
// хода даёт оценку: неточность (?!), ошибка (?) или грубая ошибка (??).
struct RvJob {
    std::vector<eng::Board> pos;   // позиции 0..n
    std::vector<eng::Move> moves;  // ходы 0..n-1
    std::vector<uint64_t> hashes;
    Uint32 per = 300;              // время на ход (мс)
    std::atomic<bool> stop{false};
    std::atomic<int> progress{0};
    std::atomic<int> running{0};
    std::vector<eng::MoveVerdict> res;
};
struct ReviewData {
    bool ready = false;
    Game g;
    int mode = MODE_BOT;
    int human = eng::WHITE;
    int focus = -1;  // чьи ошибки показывать (-1 — обе стороны)
    bool wb = true;
    std::vector<eng::Board> pos;
    std::vector<eng::MoveVerdict> res;
    std::vector<int> score;  // оценка позиции i с точки зрения того, кто ходит
    std::vector<eng::Move> best;
    std::vector<int> cls;    // 0 — нормально, 1 ?!, 2 ?, 3 ??
    std::vector<bool> isBest, book, forced;
    std::vector<int> list;   // номера ходов с ошибками для списка
    int cnt[2][4];
    int acc[2];
    int rate[2];  // общая оценка игры 1..10
    int k = 0;               // показан ход k (1..n), 0 — начало
    float scroll = 0, scrollStart = 0;
};
static ReviewData gRv;
static RvJob *gRvJob = nullptr;
static std::vector<SDL_Thread *> gRvThreads;
static bool gRvDrag = false;

struct RvPart {
    RvJob *job;
    int from, to;
};
// Поток анализа: свой отрезок партии, своя таблица позиций.
// Идём с конца отрезка: глубокие варианты поздних позиций помогают ранним.
static int SDLCALL rvWorkerFn(void *p) {
    RvPart *a = (RvPart *)p;
    RvJob *j = a->job;
    int from = a->from, to = a->to;
    delete a;
    eng::TTBuf tb;
    tb.init(18);
    for (int i = to - 1; i >= from && !j->stop.load(); i--) {
        std::vector<uint64_t> h(j->hashes.begin(), j->hashes.begin() + i + 1);
        j->res[(size_t)i] = eng::analyseMove(j->pos[(size_t)i], h, j->moves[(size_t)i], j->per, &j->stop, &tb);
        j->progress++;
    }
    j->running--;
    return 0;
}

static void cancelReview() {
    if (!gRvJob) return;
    gRvJob->stop = true;
    for (auto t : gRvThreads) SDL_WaitThread(t, nullptr);
    gRvThreads.clear();
    delete gRvJob;
    gRvJob = nullptr;
}

static float winChance(int cp) {
    if (cp > 1500) cp = 1500;
    if (cp < -1500) cp = -1500;
    return 2.0f / (1.0f + std::exp(-0.00368208f * cp)) - 1.0f;
}
static int rvWhiteScore(int i) {
    return gRv.pos[(size_t)i].side == eng::WHITE ? gRv.score[(size_t)i] : -gRv.score[(size_t)i];
}
static int rvWhite(int moveIdx, int v) { return gRv.pos[(size_t)moveIdx].side == eng::WHITE ? v : -v; }

// Ход из дебютного справочника (темы обучения «Дебюты»)
static bool rvIsBook(const Game &g, int i) {
    static std::vector<std::vector<std::string>> lines;
    if (lines.empty())
        for (const auto &p : LP_OPEN2)
            if (p.mode == LM_GAME && strcmp(p.fen, FEN_START) == 0) lines.push_back(splitWords(p.sol));
    if (!g.startFen.empty() || i >= 24) return false;
    for (auto &l : lines) {
        if ((int)l.size() <= i) continue;
        bool ok = true;
        for (int k = 0; k <= i && ok; k++)
            if (eng::toUCI(g.moves[(size_t)k]) != l[(size_t)k]) ok = false;
        if (ok) return true;
    }
    return false;
}

static double moveAccuracy(double winLossPct) {
    double a = 103.1668 * std::exp(-0.04354 * std::max(0.0, winLossPct)) - 3.1669;
    return std::max(0.0, std::min(100.0, a));
}

static void rvClassify() {
    size_t n = gRv.g.moves.size();
    gRv.score.assign(n + 1, 0);
    gRv.best.assign(n, 0);
    for (size_t i = 0; i < n; i++) {
        gRv.score[i] = gRv.res[i].best;
        gRv.best[i] = gRv.res[i].bestMove;
    }
    gRv.score[n] = n ? -gRv.res[n - 1].played : 0;
    gRv.cls.assign(n, 0);
    gRv.isBest.assign(n, false);
    gRv.book.assign(n, false);
    gRv.forced.assign(n, false);
    gRv.list.clear();
    memset(gRv.cnt, 0, sizeof(gRv.cnt));
    std::vector<double> acc(n, 100.0);
    for (size_t i = 0; i < n; i++) {
        const eng::MoveVerdict &v = gRv.res[i];
        int mover = gRv.pos[i].side;
        bool bk = rvIsBook(gRv.g, (int)i), fo = v.legal == 1;
        gRv.book[i] = bk;
        gRv.forced[i] = fo;
        float d = std::max(0.0f, winChance(v.best) - winChance(v.played));
        if (bk || fo) d = 0;
        gRv.isBest[i] = !bk && (v.bestMove == gRv.g.moves[i] || v.played >= v.best);
        int c = 0;
        if (d >= 0.30f) c = 3;
        else if (d >= 0.20f) c = 2;
        else if (d >= 0.10f) c = 1;
        gRv.cls[i] = c;
        gRv.cnt[mover][c]++;
        acc[i] = moveAccuracy(d * 50.0);
        if (c > 0 && (gRv.focus < 0 || gRv.focus == mover)) gRv.list.push_back((int)i);
    }
    // Точность как на lichess: среднее, взвешенное по остроте позиции, и гармоническое среднее
    std::vector<double> wp(n + 1);
    for (size_t i = 0; i <= n; i++) {
        int ws = gRv.pos[i].side == eng::WHITE ? gRv.score[i] : -gRv.score[i];
        wp[i] = 50.0 + 50.0 * winChance(ws);
    }
    int win = (int)std::max<size_t>(2, std::min<size_t>(8, n / 10));
    win = std::min(win, (int)n + 1);
    double wsum[2] = {0, 0}, wacc[2] = {0, 0}, hsum[2] = {0, 0};
    int cntc[2] = {0, 0};
    for (size_t i = 0; i < n; i++) {
        int st = (int)i < win - 2 ? 0 : (int)i - (win - 2);
        if (st + win > (int)n + 1) st = (int)n + 1 - win;
        double mean = 0, var = 0;
        for (int k = 0; k < win; k++) mean += wp[(size_t)(st + k)];
        mean /= win;
        for (int k = 0; k < win; k++) var += (wp[(size_t)(st + k)] - mean) * (wp[(size_t)(st + k)] - mean);
        double w = std::max(0.5, std::min(12.0, std::sqrt(var / win)));
        int m = gRv.pos[i].side;
        wsum[m] += w;
        wacc[m] += w * acc[i];
        hsum[m] += 1.0 / std::max(2.0, acc[i]);
        cntc[m]++;
    }
    for (int s = 0; s < 2; s++) {
        double a = 0;
        if (cntc[s]) a = (wacc[s] / wsum[s] + cntc[s] / hsum[s]) * 0.5;
        gRv.acc[s] = (int)std::lround(a);
        // оценка из 10: точность и штраф за грубые ошибки
        double r = a / 10.0 - 0.5 * gRv.cnt[s][3] - 0.2 * gRv.cnt[s][2] - 0.05 * gRv.cnt[s][1];
        gRv.rate[s] = cntc[s] ? (int)std::max(1L, std::min(10L, std::lround(r))) : 0;
    }
    gRv.ready = true;
}

static void startReview() {
    if (gM.g.moves.empty()) return;
    cancelBot();
    cancelReview();
    gRv = ReviewData();
    gRv.g = gM.g;
    gRv.mode = gM.mode;
    gRv.human = gM.human;
    gRv.focus = gM.mode == MODE_TWO ? -1 : gM.human;
    gRv.wb = gM.mode == MODE_TWO ? true : gM.human == eng::WHITE;
    int n = (int)gRv.g.moves.size();
    for (int i = 0; i < n; i++) gRv.pos.push_back(gRv.g.before[(size_t)i]);
    gRv.pos.push_back(gRv.g.cur);
    gRvJob = new RvJob();
    gRvJob->pos = gRv.pos;
    gRvJob->moves = gRv.g.moves;
    gRvJob->hashes = gRv.g.hashes;
    gRvJob->res.assign((size_t)n, eng::MoveVerdict());
    // потоки: на телефоне обычно 8 ядер — берём до 4, оставляя ядро интерфейсу
    int cpu = SDL_GetCPUCount();
    int K = cpu >= 4 ? std::min(4, cpu - 1) : std::max(1, cpu);
    K = std::max(1, std::min(K, n));
    int wall = std::max(8000, std::min(35000, 4000 + 350 * n));  // общее время анализа, мс
    gRvJob->per = (Uint32)std::max(120, std::min(3000, (int)(wall * K / (n * 1.7))));
    gRvJob->running = K;
    for (int k = 0; k < K; k++) {
        RvPart *p = new RvPart;
        p->job = gRvJob;
        p->from = n * k / K;
        p->to = n * (k + 1) / K;
        SDL_Thread *t = SDL_CreateThreadWithStackSize(rvWorkerFn, "shahreview", 4 * 1024 * 1024, p);
        if (t) gRvThreads.push_back(t);
        else rvWorkerFn(p);  // без потока — считаем здесь
    }
    gOverlay = OV_NONE;
    clearSel();
    gScreen = SC_REVIEW;
}

static void pollReview() {
    if (gRvJob && gRvJob->running.load() == 0) {
        for (auto t : gRvThreads) SDL_WaitThread(t, nullptr);
        gRvThreads.clear();
        gRv.res = gRvJob->res;
        delete gRvJob;
        gRvJob = nullptr;
        rvClassify();
        gRv.k = gRv.list.empty() ? 0 : gRv.list[0] + 1;
        playSound(SND_END);
    }
}

static int rvNextMistake(int k) {
    for (int i : gRv.list)
        if (i + 1 > k) return i + 1;
    return k;
}

static void leaveReview() {
    cancelReview();
    gScreen = SC_GAME;
    gLastTick = SDL_GetTicks();
}

// =====================================================================
//                 РАССТАНОВКА ФИГУР (РЕДАКТОР ПОЗИЦИИ)
// =====================================================================
static int gEdSq[64];
static int gEdSide = eng::WHITE;
static int gEdTool = 0;        // фигура для расстановки, 0 — ластик
static bool gEdInit = false;
static int gEdFrom = -1;       // клетка, с которой тянем фигуру
static bool gEdDown = false;
static bool gEdMoved = false;
static std::string gCustomFen; // позиция для следующей партии (пусто — обычная)
static const int ED_TYPES[6] = {eng::KING, eng::QUEEN, eng::ROOK, eng::BISHOP, eng::KNIGHT, eng::PAWN};

static void edLoadBoard(const eng::Board &b) {
    for (int i = 0; i < 64; i++) gEdSq[i] = b.sq[i];
    gEdSide = b.side;
}
static void edEnsure() {
    if (gEdInit) return;
    eng::Board b;
    b.setStart();
    edLoadBoard(b);
    gEdTool = eng::mkPiece(eng::WHITE, eng::QUEEN);
    gEdInit = true;
}

// FEN из расстановки; рокировка разрешена, если король и ладья на своих местах
static std::string edFen() {
    std::string s;
    for (int r = 7; r >= 0; r--) {
        int e = 0;
        for (int f = 0; f < 8; f++) {
            int p = gEdSq[r * 8 + f];
            if (!p) {
                e++;
                continue;
            }
            if (e) s += (char)('0' + e);
            e = 0;
            char c = " pnbrqk"[eng::pType(p)];
            if (eng::pColor(p) == eng::WHITE) c = (char)(c - 32);
            s += c;
        }
        if (e) s += (char)('0' + e);
        if (r) s += '/';
    }
    s += gEdSide == eng::WHITE ? " w " : " b ";
    std::string c;
    int WK = eng::mkPiece(eng::WHITE, eng::KING), WR = eng::mkPiece(eng::WHITE, eng::ROOK);
    int BK = eng::mkPiece(eng::BLACK, eng::KING), BR = eng::mkPiece(eng::BLACK, eng::ROOK);
    if (gEdSq[4] == WK && gEdSq[7] == WR) c += 'K';
    if (gEdSq[4] == WK && gEdSq[0] == WR) c += 'Q';
    if (gEdSq[60] == BK && gEdSq[63] == BR) c += 'k';
    if (gEdSq[60] == BK && gEdSq[56] == BR) c += 'q';
    s += c.empty() ? "-" : c;
    s += " - 0 1";
    return s;
}

static void edCount(int color, int &total, int &pawns) {
    total = pawns = 0;
    for (int i = 0; i < 64; i++) {
        int p = gEdSq[i];
        if (p && eng::pColor(p) == color) {
            total++;
            if (eng::pType(p) == eng::PAWN) pawns++;
        }
    }
}

// Поставить фигуру; toggle — та же фигура на клетке убирается
static bool edPlace(int sq, int piece, bool toggle) {
    if (toggle && gEdSq[sq] == piece) {
        gEdSq[sq] = 0;
        return true;
    }
    int t = eng::pType(piece), c = eng::pColor(piece);
    if (t == eng::PAWN && (sq < 8 || sq >= 56)) {
        toast("ПЕШКИ НЕ СТОЯТ НА 1 И 8 ГОРИЗОНТАЛИ");
        return false;
    }
    int total = 0, pawns = 0;
    for (int i = 0; i < 64; i++) {
        int p = gEdSq[i];
        if (i == sq || !p || eng::pColor(p) != c) continue;
        if (t == eng::KING && p == piece) continue;  // старый король уйдёт
        total++;
        if (eng::pType(p) == eng::PAWN) pawns++;
    }
    if (total >= 16) {
        toast("НЕ БОЛЬШЕ 16 ФИГУР У СТОРОНЫ");
        return false;
    }
    if (t == eng::PAWN && pawns >= 8) {
        toast("НЕ БОЛЬШЕ 8 ПЕШЕК У СТОРОНЫ");
        return false;
    }
    if (t == eng::KING)
        for (int i = 0; i < 64; i++)
            if (i != sq && gEdSq[i] == piece) gEdSq[i] = 0;
    gEdSq[sq] = piece;
    return true;
}

static void edTap(int sq) {
    if (gEdTool == 0) {
        if (gEdSq[sq]) playSound(SND_CAPTURE);
        gEdSq[sq] = 0;
        return;
    }
    if (edPlace(sq, gEdTool, true)) playSound(SND_MOVE);
}

static void edMove(int from, int to) {
    if (from == to) return;
    int p = gEdSq[from];
    if (!p) return;
    gEdSq[from] = 0;
    if (edPlace(to, p, false)) playSound(SND_MOVE);
    else gEdSq[from] = p;
}

// Проверка позиции перед игрой
static bool edCheck(std::string &msg) {
    int wk = 0, bk = 0;
    for (int i = 0; i < 64; i++) {
        if (gEdSq[i] == eng::mkPiece(eng::WHITE, eng::KING)) wk++;
        if (gEdSq[i] == eng::mkPiece(eng::BLACK, eng::KING)) bk++;
    }
    if (!wk) { msg = "ПОСТАВЬТЕ БЕЛОГО КОРОЛЯ"; return false; }
    if (!bk) { msg = "ПОСТАВЬТЕ ЧЁРНОГО КОРОЛЯ"; return false; }
    eng::Board b;
    if (!b.setFEN(edFen())) { msg = "ОШИБКА В ПОЗИЦИИ"; return false; }
    {
        int a = b.kingSq[0], c = b.kingSq[1];
        if (std::abs((a & 7) - (c & 7)) <= 1 && std::abs((a >> 3) - (c >> 3)) <= 1) {
            msg = "КОРОЛИ НЕ МОГУТ СТОЯТЬ РЯДОМ";
            return false;
        }
    }
    int other = b.side ^ 1;
    if (b.inCheck(other)) {
        msg = std::string("ШАХ ") + (other == eng::WHITE ? "БЕЛЫМ" : "ЧЁРНЫМ") + ", А ХОДЯТ " +
              (b.side == eng::WHITE ? "БЕЛЫЕ" : "ЧЁРНЫЕ");
        return false;
    }
    eng::MoveList ml;
    b.genLegal(ml);
    if (!ml.n) {
        msg = b.inCheck(b.side) ? "В ЭТОЙ ПОЗИЦИИ УЖЕ МАТ" : "В ЭТОЙ ПОЗИЦИИ УЖЕ ПАТ";
        return false;
    }
    if (b.insufficient()) { msg = "НЕ ХВАТАЕТ ФИГУР ДЛЯ МАТА"; return false; }
    msg = "ПОЗИЦИЯ ГОТОВА К ИГРЕ";
    return true;
}

static void edClear() {
    int wk = -1, bk = -1;
    for (int i = 0; i < 64; i++) {
        if (gEdSq[i] == eng::mkPiece(eng::WHITE, eng::KING)) wk = i;
        if (gEdSq[i] == eng::mkPiece(eng::BLACK, eng::KING)) bk = i;
        gEdSq[i] = 0;
    }
    gEdSq[wk >= 0 ? wk : 4] = eng::mkPiece(eng::WHITE, eng::KING);
    gEdSq[bk >= 0 ? bk : 60] = eng::mkPiece(eng::BLACK, eng::KING);
}

// =====================================================================
//                         РАЗМЕТКА И КНОПКИ
// =====================================================================
enum {
    B_NONE = 0,
    B_CONTINUE, B_PLAY_BOT, B_PLAY_TWO, B_STATS, B_SOUND, B_EXIT,
    B_LVL1, B_LVL2, B_LVL3, B_LVL4, B_LVL5,
    B_COL_W, B_COL_B, B_COL_R,
    B_CLK0, B_CLK1, B_CLK2, B_CLK3,
    B_START, B_BACK,
    B_UNDO, B_RESIGN, B_NEW, B_FLIP, B_MENU,
    B_YES, B_NO,
    B_RES_NEW, B_RES_MENU, B_RES_VIEW,
    B_PROMO_Q, B_PROMO_R, B_PROMO_B, B_PROMO_N,
    B_RESET,
    B_LEARN, B_L_PREV, B_L_MID, B_L_NEXT,
    B_PLAY_NET, B_NET_HOST, B_NET_JOIN, B_NET_CANCEL, B_NET_MANUAL, B_NET_GO, B_DRAW,
    B_KEY0, B_KEY1, B_KEY2, B_KEY3, B_KEY4, B_KEY5, B_KEY6, B_KEY7, B_KEY8, B_KEY9, B_KEY_DOT, B_KEY_DEL,
    B_FOUND0, B_FOUND1, B_FOUND2, B_FOUND3, B_FOUND4, B_FOUND5,
    B_NAV_FIRST, B_NAV_PREV, B_NAV_NEXT, B_NAV_LAST, B_ARROWS,
    B_LG_FIRST, B_LG_PREV, B_LG_PLAY, B_LG_NEXT, B_LG_LAST,
    B_EDITOR, B_ED_PAL0, B_ED_PAL_END = B_ED_PAL0 + 11, B_ED_ERASER, B_ED_WHITE, B_ED_BLACK, B_ED_CLEAR, B_ED_START,
    B_ED_GAME, B_ED_PLAY, B_ED_BOT, B_ED_TWO,
    B_REVIEW, B_RES_REVIEW, B_RV_FIRST, B_RV_PREV, B_RV_NEXT, B_RV_LAST, B_RV_MIST, B_RV_DONE,
    B_CH0  // B_CH0 + номер темы — должна быть последней
};
enum { ST_NORMAL, ST_PRIMARY, ST_DANGER, ST_SEG, ST_TOOL };
enum { IC_NONE, IC_UNDO, IC_FLAG, IC_PLUS, IC_FLIP, IC_MENU, IC_EQUAL, IC_FIRST, IC_PREV, IC_NEXT, IC_LAST, IC_SEARCH, IC_PENCIL, IC_ERASER };

struct Btn {
    SDL_FRect r;
    int id;
    std::string label;
    int style;
    bool enabled;
    bool selected;
    int icon;
    int piece;
    int ts;
};
static std::vector<Btn> gScreenBtns, gOverBtns;
static int gPressed = -1;

static Btn mkBtn(float x, float y, float w, float h, int id, const std::string &label, int style, int ts) {
    Btn b;
    b.r.x = x; b.r.y = y; b.r.w = w; b.r.h = h;
    b.id = id;
    b.label = label;
    b.style = style;
    b.enabled = true;
    b.selected = false;
    b.icon = IC_NONE;
    b.piece = 0;
    b.ts = ts;
    return b;
}
static bool inRect(const SDL_FRect &r, float x, float y) {
    return x >= r.x && y >= r.y && x < r.x + r.w && y < r.y + r.h;
}

static float uiU() { return std::min((float)gW, gH * 0.56f) / 100.0f; }
static int uiTS() { return std::max(1, (int)std::lround(uiU() * 0.52f)); }

struct LessonLayout {
    float top, pad, hdrY, titleY, bx, by, cell, S, statusY, textX, textY, textW, textH, btnY, btnH;
    int ts, tsT, tsB;
};
static LessonLayout lessonLayout() {
    LessonLayout L;
    float W = (float)gW, H = (float)gH, U = uiU();
    L.top = H * 0.05f;
    L.pad = std::max(6.0f, U * 4.0f);
    L.ts = uiTS();
    L.tsT = L.ts + 2;
    L.tsB = std::max(1, (int)std::lround(U * 0.46f));
    L.hdrY = L.top + U * 2;
    L.titleY = L.hdrY + textH(std::max(1, L.ts - 1)) + U * 2.5f;
    L.btnH = std::max(40.0f, U * 13.0f);
    L.btnY = H - U * 4 - L.btnH;
    float S = std::min(W - 2 * L.pad, H * 0.38f);
    float cell = std::floor(S / 8.0f);
    if (cell < 6) cell = 6;
    L.cell = cell;
    L.S = cell * 8;
    L.bx = std::floor((W - L.S) * 0.5f);
    L.by = std::floor(L.titleY + textH(L.tsT) + U * 4);
    L.statusY = L.by + L.S + U * 3;
    int md = curPage().mode;
    float statusH = md == LM_SHOW ? 0.0f : md == LM_GAME ? std::max(36.0f, U * 11.0f) + U * 3 : textH(L.ts) + U * 3;
    L.textX = L.pad;
    L.textW = W - 2 * L.pad;
    L.textY = L.statusY + statusH;
    L.textH = L.btnY - U * 3 - L.textY;
    return L;
}

struct EdLayout {
    float pad, titleY, bx, by, cell, S, palY1, palY2, palW, palH, palGap, infoY, opt1Y, opt2Y, optH, btnY, btnH;
    int ts, tsS;
};
static EdLayout edLayout() {
    EdLayout L;
    float W = (float)gW, H = (float)gH, U = uiU();
    L.pad = std::max(6.0f, U * 3.0f);
    L.ts = uiTS();
    L.tsS = std::max(1, (int)std::lround(U * 0.42f));
    L.titleY = H * 0.05f + U * 2;
    L.btnH = std::max(40.0f, U * 13.0f);
    L.btnY = H - U * 4 - L.btnH;
    L.optH = std::max(34.0f, U * 10.5f);
    L.opt2Y = L.btnY - U * 2.5f - L.optH;
    L.opt1Y = L.opt2Y - U * 2 - L.optH;
    float infoH = textH(L.tsS) * 2 + U * 3;
    L.infoY = L.opt1Y - U * 2 - infoH;
    L.palGap = U * 1.5f;
    L.palW = (W - 2 * L.pad - 6 * L.palGap) / 7;
    L.palH = std::min(L.palW, U * 12.0f);
    L.palY2 = L.infoY - U * 2 - L.palH;
    L.palY1 = L.palY2 - L.palGap - L.palH;
    float zoneTop = L.titleY + textH(L.ts + 1) + U * 3, zoneBot = L.palY1 - U * 3;
    float S = std::min(W - 2 * L.pad, zoneBot - zoneTop);
    L.cell = std::max(6.0f, std::floor(S / 8.0f));
    L.S = L.cell * 8;
    L.bx = std::floor((W - L.S) * 0.5f);
    L.by = std::floor(zoneTop + std::max(0.0f, (zoneBot - zoneTop - L.S) * 0.5f));
    return L;
}

struct RvLayout {
    float top, pad, titleY, rateY, sumY, bx, by, cell, S, evalY, evalH, infoY, listY, listH, rowH, navY, navH, btnY, btnH;
    int ts, tsS;
};
static RvLayout rvLayout() {
    RvLayout L;
    float W = (float)gW, H = (float)gH, U = uiU();
    L.top = H * 0.05f;
    L.pad = std::max(6.0f, U * 3.0f);
    L.ts = uiTS();
    L.tsS = std::max(1, (int)std::lround(U * 0.42f));
    L.titleY = L.top + U * 2;
    L.rateY = L.titleY + textH(L.ts + 1) + U * 3;
    L.sumY = L.rateY + textH(L.ts + 2) + U * 4;
    float sumH = 2 * (textH(L.tsS) + U * 2);
    L.btnH = std::max(40.0f, U * 13.0f);
    L.btnY = H - U * 4 - L.btnH;
    L.navH = std::max(34.0f, U * 10.5f);
    L.navY = L.btnY - U * 2.5f - L.navH;
    float S = std::min(W - 2 * L.pad, H * 0.34f);
    L.cell = std::max(6.0f, std::floor(S / 8.0f));
    L.S = L.cell * 8;
    L.bx = std::floor((W - L.S) * 0.5f);
    L.by = std::floor(L.sumY + sumH + U * 2);
    L.evalY = L.by + L.S + U * 1.5f;
    L.evalH = std::max(4.0f, U * 1.8f);
    L.infoY = L.evalY + L.evalH + U * 3;
    float infoH = textH(L.ts) + U * 2 + 2 * (textH(L.tsS) + U * 2);
    L.listY = L.infoY + infoH + U * 1;
    L.listH = L.navY - U * 2 - L.listY;
    L.rowH = textH(L.tsS) + U * 3;
    return L;
}

struct GameLayout {
    float top, pad, barH, btnH, bx, by, cell, S, topBarY, botBarY, listX, listY, listW, listH, btnY, navY, navH;
    int ts, tsSmall;
};

static GameLayout gameLayout() {
    GameLayout L;
    float W = (float)gW, H = (float)gH;
    float U = uiU();
    L.top = H * 0.05f;
    L.pad = std::max(4.0f, U * 2.0f);
    L.barH = std::max(26.0f, U * 10.5f);
    L.btnH = std::max(40.0f, U * 15.0f);
    float minList = std::max(36.0f, U * 13.0f);
    float avail = H - L.top - 2 * L.barH - L.btnH - minList - L.pad * 4.0f;
    float S = std::min(W - 2 * L.pad - 2, avail);
    float cell = std::floor(S / 8.0f);
    if (cell < 8) cell = 8;
    L.cell = cell;
    L.S = cell * 8;
    float y = L.top + L.pad * 0.5f;
    L.topBarY = y;
    y += L.barH + L.pad * 0.3f;
    L.bx = std::floor((W - L.S) * 0.5f);
    L.by = std::floor(y);
    y = L.by + L.S + L.pad * 0.3f;
    L.botBarY = y;
    y += L.barH;
    L.btnY = H - L.pad - L.btnH;
    L.listX = L.pad;
    L.listY = y + L.pad * 0.5f;
    L.listW = W - 2 * L.pad;
    L.listH = L.btnY - L.pad * 0.6f - L.listY;
    L.navH = std::max(30.0f, U * 9.5f);
    L.navY = L.listY + L.listH - L.navH - U * 1.8f;
    L.ts = uiTS();
    L.tsSmall = std::max(1, (int)std::lround(U * 0.42f));
    return L;
}

static bool whiteBottom() {
    bool base = gM.mode != MODE_TWO ? gM.human == eng::WHITE : gViewSide == eng::WHITE;
    return base != gM.flip;
}

static void sqToXY(const GameLayout &L, int s, float &x, float &y) {
    int f = s & 7, r = s >> 3;
    int col, row;
    if (whiteBottom()) { col = f; row = 7 - r; }
    else { col = 7 - f; row = r; }
    x = L.bx + col * L.cell;
    y = L.by + row * L.cell;
}
static int xyToSq(const GameLayout &L, float x, float y) {
    if (x < L.bx || y < L.by || x >= L.bx + L.S || y >= L.by + L.S) return -1;
    int col = (int)((x - L.bx) / L.cell), row = (int)((y - L.by) / L.cell);
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    if (whiteBottom()) return (7 - row) * 8 + col;
    return row * 8 + (7 - col);
}

static const char *LEVEL_NAME[6] = {"", "НОВИЧОК", "ЛЮБИТЕЛЬ", "СРЕДНИЙ", "ОПЫТНЫЙ", "МАСТЕР"};

struct MenuM {
    float ps, oy, ty, btnY, bw, bh, gap;
    int tts, sts;
    bool cont;
};
static MenuM menuMetrics() {
    MenuM m;
    float W = (float)gW, H = (float)gH, U = uiU();
    float top = H * 0.05f;
    m.cont = gM.active && gM.g.result == RES_NONE;
    m.bw = std::min(W * 0.82f, U * 82.0f);
    m.bh = std::max(40.0f, U * 14.0f);
    m.gap = U * 3.2f;
    int rows = m.cont ? 6 : 5;
    float total = rows * m.bh + (rows - 1) * m.gap;
    m.ps = std::min(W * 0.36f, H * 0.17f);
    m.tts = std::max(2, std::min((int)(W * 0.8f / (7 * 6)), (int)(H * 0.075f / 7)));
    m.sts = std::max(1, m.tts / 3);
    float titleH = m.ps + U * 3 + textH(m.tts) + U * 3 + textH(m.sts);
    float block = titleH + U * 12 + total;
    m.oy = top + std::max(U * 3, (H - top - block) * 0.42f);
    m.ty = m.oy + m.ps + U * 3;
    m.btnY = m.oy + titleH + U * 12;
    if (m.btnY + total > H - U * 4) m.btnY = H - U * 4 - total;
    return m;
}

static void buildScreenButtons() {
    gScreenBtns.clear();
    float W = (float)gW, H = (float)gH, U = uiU();
    int ts = uiTS();
    if (gScreen == SC_MENU) {
        MenuM mm = menuMetrics();
        float bw = mm.bw, bh = mm.bh, gap = mm.gap;
        float x = (W - bw) * 0.5f;
        bool cont = mm.cont;
        float y = mm.btnY;
        int bts = ts + 1;
        if (cont) {
            gScreenBtns.push_back(mkBtn(x, y, bw, bh, B_CONTINUE, "ПРОДОЛЖИТЬ", ST_PRIMARY, bts));
            y += bh + gap;
        }
        gScreenBtns.push_back(mkBtn(x, y, bw, bh, B_PLAY_BOT, "ИГРА С БОТОМ", cont ? ST_NORMAL : ST_PRIMARY, bts));
        y += bh + gap;
        {
            float hw = (bw - gap) * 0.5f;
            gScreenBtns.push_back(mkBtn(x, y, hw, bh, B_PLAY_TWO, "ВДВОЁМ", ST_NORMAL, bts));
            gScreenBtns.push_back(mkBtn(x + hw + gap, y, hw, bh, B_PLAY_NET, "ПО СЕТИ", ST_NORMAL, bts));
        }
        y += bh + gap;
        gScreenBtns.push_back(mkBtn(x, y, bw, bh, B_EDITOR, "РАССТАНОВКА ФИГУР", ST_NORMAL, bts));
        y += bh + gap;
        {
            float hw = (bw - gap) * 0.5f;
            gScreenBtns.push_back(mkBtn(x, y, hw, bh, B_LEARN, "ОБУЧЕНИЕ", ST_NORMAL, bts));
            gScreenBtns.push_back(mkBtn(x + hw + gap, y, hw, bh, B_STATS, "СТАТИСТИКА", ST_NORMAL, bts));
        }
        y += bh + gap;
        float hw = (bw - gap) * 0.5f;
        gScreenBtns.push_back(mkBtn(x, y, hw, bh, B_SOUND, gSoundOn ? "ЗВУК: ВКЛ" : "ЗВУК: ВЫКЛ", ST_NORMAL, ts));
        gScreenBtns.push_back(mkBtn(x + hw + gap, y, hw, bh, B_EXIT, "ВЫХОД", ST_NORMAL, ts));
    } else if (gScreen == SC_SETUP) {
        float bw = std::min(W * 0.9f, U * 90.0f), x = (W - bw) * 0.5f;
        float bh = std::max(36.0f, U * 12.5f), gap = U * 2.0f;
        float y = H * 0.05f + U * 26.0f;
        if (gSetupMode == MODE_BOT) {
            y += textH(ts) + U * 3;
            float sw = (bw - 4 * gap) / 5;
            for (int i = 0; i < 5; i++) {
                Btn b = mkBtn(x + i * (sw + gap), y, sw, bh, B_LVL1 + i, std::to_string(i + 1), ST_SEG, ts + 2);
                b.selected = gSet.level == i + 1;
                gScreenBtns.push_back(b);
            }
            y += bh + U * 3 + textH(ts) + U * 7;
            y += textH(ts) + U * 3;
            float cw = (bw - 2 * gap) / 3;
            const char *cl[3] = {"БЕЛЫЕ", "ЧЁРНЫЕ", "СЛУЧАЙНО"};
            for (int i = 0; i < 3; i++) {
                Btn b = mkBtn(x + i * (cw + gap), y, cw, bh * 1.35f, B_COL_W + i, cl[i], ST_SEG, ts);
                b.selected = gSet.color == i;
                b.piece = i == 0 ? eng::mkPiece(eng::WHITE, eng::KING) : (i == 1 ? eng::mkPiece(eng::BLACK, eng::KING) : -1);
                gScreenBtns.push_back(b);
            }
            y += bh * 1.35f + U * 7;
        }
        y += textH(ts) + U * 3;
        float kw = (bw - 3 * gap) / 4;
        const char *kl[4] = {"НЕТ", "5 МИН", "10 МИН", "15 МИН"};
        for (int i = 0; i < 4; i++) {
            Btn b = mkBtn(x + i * (kw + gap), y, kw, bh, B_CLK0 + i, kl[i], ST_SEG, ts);
            b.selected = gSet.clock == i;
            gScreenBtns.push_back(b);
        }
        float bh2 = std::max(40.0f, U * 14.0f);
        float yb = H - U * 6 - bh2;
        gScreenBtns.push_back(mkBtn(x, yb - bh2 - U * 3, bw, bh2, B_START, "НАЧАТЬ ИГРУ", ST_PRIMARY, ts + 1));
        gScreenBtns.push_back(mkBtn(x, yb, bw, bh2, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
    } else if (gScreen == SC_NET) {
        float bw = std::min(W * 0.9f, U * 90.0f), x = (W - bw) * 0.5f;
        float bh = std::max(36.0f, U * 12.5f), gap = U * 2.0f;
        float bh2 = std::max(40.0f, U * 14.0f);
        float yb = H - U * 6 - bh2;
        float top = H * 0.05f;
        if (gNetUI == NU_MENU) {
            float y = top + U * 30 + textH(ts) + U * 3;
            float cw = (bw - 2 * gap) / 3;
            const char *cl[3] = {"БЕЛЫЕ", "ЧЁРНЫЕ", "СЛУЧАЙНО"};
            for (int i = 0; i < 3; i++) {
                Btn b = mkBtn(x + i * (cw + gap), y, cw, bh * 1.35f, B_COL_W + i, cl[i], ST_SEG, ts);
                b.selected = gSet.color == i;
                b.piece = i == 0 ? eng::mkPiece(eng::WHITE, eng::KING) : (i == 1 ? eng::mkPiece(eng::BLACK, eng::KING) : -1);
                gScreenBtns.push_back(b);
            }
            y += bh * 1.35f + U * 7 + textH(ts) + U * 3;
            float kw = (bw - 3 * gap) / 4;
            const char *kl[4] = {"НЕТ", "5 МИН", "10 МИН", "15 МИН"};
            for (int i = 0; i < 4; i++) {
                Btn b = mkBtn(x + i * (kw + gap), y, kw, bh, B_CLK0 + i, kl[i], ST_SEG, ts);
                b.selected = gSet.clock == i;
                gScreenBtns.push_back(b);
            }
            gScreenBtns.push_back(mkBtn(x, yb - 2 * (bh2 + U * 3), bw, bh2, B_NET_HOST, "СОЗДАТЬ ИГРУ", ST_PRIMARY, ts + 1));
            gScreenBtns.push_back(mkBtn(x, yb - (bh2 + U * 3), bw, bh2, B_NET_JOIN, "ПОДКЛЮЧИТЬСЯ", ST_NORMAL, ts + 1));
            gScreenBtns.push_back(mkBtn(x, yb, bw, bh2, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
        } else if (gNetUI == NU_JOIN) {
            float y = top + U * 36;
            for (int i = 0; i < (int)gFound.size() && i < 4; i++) {
                gScreenBtns.push_back(mkBtn(x, y, bw, bh2, B_FOUND0 + i, foundLabel(gFound[i]), ST_PRIMARY, ts));
                y += bh2 + U * 3;
            }
            gScreenBtns.push_back(mkBtn(x, yb - (bh2 + U * 3), bw, bh2, B_NET_MANUAL, "ВВЕСТИ АДРЕС", ST_NORMAL, ts + 1));
            gScreenBtns.push_back(mkBtn(x, yb, bw, bh2, B_NET_CANCEL, "НАЗАД", ST_NORMAL, ts + 1));
        } else if (gNetUI == NU_KEYPAD) {
            float y = top + U * 30 + U * 14 + U * 5;
            float kw = (bw - 2 * gap) / 3;
            float avail = yb - (bh2 + U * 3) - U * 4 - y;
            float kh = std::min(U * 13.0f, (avail - 3 * gap) / 4);
            const char *keys[12] = {"1", "2", "3", "4", "5", "6", "7", "8", "9", ".", "0", "СТЕРЕТЬ"};
            int kid[12] = {B_KEY1, B_KEY2, B_KEY3, B_KEY4, B_KEY5, B_KEY6, B_KEY7, B_KEY8, B_KEY9, B_KEY_DOT, B_KEY0, B_KEY_DEL};
            for (int i = 0; i < 12; i++)
                gScreenBtns.push_back(mkBtn(x + (i % 3) * (kw + gap), y + (i / 3) * (kh + gap), kw, kh, kid[i], keys[i],
                                            i == 11 ? ST_DANGER : ST_NORMAL, i < 11 ? ts + 2 : ts));
            gScreenBtns.push_back(mkBtn(x, yb - (bh2 + U * 3), bw, bh2, B_NET_GO, "ПОДКЛЮЧИТЬСЯ", ST_PRIMARY, ts + 1));
            gScreenBtns.push_back(mkBtn(x, yb, bw, bh2, B_NET_CANCEL, "НАЗАД", ST_NORMAL, ts + 1));
        } else {
            gScreenBtns.push_back(mkBtn(x, yb, bw, bh2, B_NET_CANCEL, "ОТМЕНА", ST_NORMAL, ts + 1));
        }
    } else if (gScreen == SC_EDITOR) {
        EdLayout L = edLayout();
        for (int c = 0; c < 2; c++)
            for (int i = 0; i < 6; i++) {
                Btn b = mkBtn(L.pad + i * (L.palW + L.palGap), c ? L.palY2 : L.palY1, L.palW, L.palH, B_ED_PAL0 + c * 6 + i, "",
                              ST_SEG, ts);
                b.piece = eng::mkPiece(c, ED_TYPES[i]);
                b.selected = gEdTool == b.piece;
                gScreenBtns.push_back(b);
            }
        Btn er = mkBtn(L.pad + 6 * (L.palW + L.palGap), L.palY1, L.palW, 2 * L.palH + L.palGap, B_ED_ERASER, "", ST_TOOL, ts);
        er.icon = IC_ERASER;
        er.selected = gEdTool == 0;
        gScreenBtns.push_back(er);
        float g = U * 2.0f, fw = W - 2 * L.pad;
        float hw = (fw - g) * 0.5f;
        Btn sw = mkBtn(L.pad, L.opt1Y, hw, L.optH, B_ED_WHITE, "ХОДЯТ БЕЛЫЕ", ST_SEG, ts);
        sw.selected = gEdSide == eng::WHITE;
        Btn sb = mkBtn(L.pad + hw + g, L.opt1Y, hw, L.optH, B_ED_BLACK, "ХОДЯТ ЧЁРНЫЕ", ST_SEG, ts);
        sb.selected = gEdSide == eng::BLACK;
        gScreenBtns.push_back(sw);
        gScreenBtns.push_back(sb);
        float tw = (fw - 2 * g) / 3;
        gScreenBtns.push_back(mkBtn(L.pad, L.opt2Y, tw, L.optH, B_ED_CLEAR, "ОЧИСТИТЬ", ST_NORMAL, ts));
        gScreenBtns.push_back(mkBtn(L.pad + tw + g, L.opt2Y, tw, L.optH, B_ED_START, "НАЧАЛЬНАЯ", ST_NORMAL, ts));
        Btn fg = mkBtn(L.pad + 2 * (tw + g), L.opt2Y, tw, L.optH, B_ED_GAME, "ИЗ ПАРТИИ", ST_NORMAL, ts);
        fg.enabled = gM.active;
        gScreenBtns.push_back(fg);
        float bw1 = fw * 0.38f;
        gScreenBtns.push_back(mkBtn(L.pad, L.btnY, bw1, L.btnH, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
        gScreenBtns.push_back(mkBtn(L.pad + bw1 + g, L.btnY, fw - bw1 - g, L.btnH, B_ED_PLAY, "ИГРАТЬ", ST_PRIMARY, ts + 1));
    } else if (gScreen == SC_REVIEW) {
        RvLayout L = rvLayout();
        int n = (int)gRv.g.moves.size();
        if (gRv.ready) {
            float g = U * 1.6f;
            float wM = (W - 2 * L.pad) * 0.34f;
            float wS = (W - 2 * L.pad - wM - 4 * g) / 4;
            int ids[5] = {B_RV_FIRST, B_RV_PREV, B_RV_NEXT, B_RV_LAST, B_RV_MIST};
            int ics[5] = {IC_FIRST, IC_PREV, IC_NEXT, IC_LAST, IC_NONE};
            float x = L.pad;
            for (int i = 0; i < 5; i++) {
                float w = i == 4 ? wM : wS;
                Btn b = mkBtn(x, L.navY, w, L.navH, ids[i], i == 4 ? "СЛЕД. ОШИБКА" : "", i == 4 ? ST_NORMAL : ST_TOOL, ts);
                b.icon = ics[i];
                if (i < 2) b.enabled = gRv.k > 0;
                else if (i < 4) b.enabled = gRv.k < n;
                else b.enabled = rvNextMistake(gRv.k) != gRv.k;
                gScreenBtns.push_back(b);
                x += w + g;
            }
        }
        gScreenBtns.push_back(mkBtn(L.pad, L.btnY, W - 2 * L.pad, L.btnH, B_RV_DONE, gRv.ready ? "К ПАРТИИ" : "ОТМЕНА",
                                    ST_PRIMARY, ts + 1));
    } else if (gScreen == SC_LEARN) {
        float bw = std::min(W * 0.9f, U * 90.0f), x = (W - bw) * 0.5f;
        float top = H * 0.05f;
        float y0 = top + U * 6 + textH(ts * 2) + U * 3 + textH(std::max(1, ts - 1)) + U * 5;
        float bhB = std::max(40.0f, U * 13.0f);
        float yb = H - U * 4 - bhB;
        float gap = U * 1.8f;
        float bh = std::min(U * 13.5f, (yb - U * 4 - y0 - (NCHAP - 1) * gap) / NCHAP);
        for (int i = 0; i < NCHAP; i++) gScreenBtns.push_back(mkBtn(x, y0 + i * (bh + gap), bw, bh, B_CH0 + i, "", ST_NORMAL, ts));
        gScreenBtns.push_back(mkBtn(x, yb, bw, bhB, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
    } else if (gScreen == SC_LESSON) {
        LessonLayout L = lessonLayout();
        float gap = U * 2.0f;
        float bw = (W - 2 * L.pad - 2 * gap) / 3;
        const LPage &p = curPage();
        bool last = gLPg >= CHAPTERS[gLCh].n - 1;
        Btn prev = mkBtn(L.pad, L.btnY, bw, L.btnH, B_L_PREV, "НАЗАД", ST_NORMAL, ts);
        prev.enabled = gLPg > 0;
        std::string mid = (p.mode == LM_SHOW || p.mode == LM_GAME) ? "ТЕМЫ" : p.mode == LM_MOVES ? "СБРОС" : (gLStatus == 1 ? "СНОВА" : "ПОДСКАЗКА");
        if (p.mode == LM_GAME) {
            float ch = std::max(36.0f, U * 11.0f), cg = U * 1.6f;
            float wPlay = (W - 2 * L.pad) * 0.32f;
            float wSmall = (W - 2 * L.pad - wPlay - 4 * cg) / 4;
            float cx = L.pad;
            int ids[5] = {B_LG_FIRST, B_LG_PREV, B_LG_PLAY, B_LG_NEXT, B_LG_LAST};
            int ics[5] = {IC_FIRST, IC_PREV, IC_NONE, IC_NEXT, IC_LAST};
            int n = (int)gLGMoves.size();
            for (int i = 0; i < 5; i++) {
                float w = i == 2 ? wPlay : wSmall;
                std::string lbl = i == 2 ? (gLGAuto ? "ПАУЗА" : (gLGPly >= n ? "СНАЧАЛА" : "СМОТРЕТЬ")) : "";
                Btn b = mkBtn(cx, L.statusY, w, ch, ids[i], lbl, i == 2 ? ST_PRIMARY : ST_TOOL, ts);
                b.icon = ics[i];
                if (i < 2) b.enabled = gLGPly > 0;
                if (i > 2) b.enabled = gLGPly < n;
                gScreenBtns.push_back(b);
                cx += w + cg;
            }
        }
        Btn m = mkBtn(L.pad + bw + gap, L.btnY, bw, L.btnH, B_L_MID, mid, ST_NORMAL, ts);
        std::string nx = !last ? "ДАЛЕЕ" : (gLCh < NCHAP - 1 ? "ДАЛЕЕ" : "ГОТОВО");
        Btn n = mkBtn(L.pad + 2 * (bw + gap), L.btnY, bw, L.btnH, B_L_NEXT, nx, ST_PRIMARY, ts);
        gScreenBtns.push_back(prev);
        gScreenBtns.push_back(m);
        gScreenBtns.push_back(n);
    } else if (gScreen == SC_STATS) {
        float bw = std::min(W * 0.82f, U * 82.0f), x = (W - bw) * 0.5f, bh = std::max(40.0f, U * 14.0f);
        float yb = H - U * 6 - bh;
        gScreenBtns.push_back(mkBtn(x, yb - bh - U * 3, bw, bh, B_RESET, "СБРОСИТЬ", ST_DANGER, ts + 1));
        gScreenBtns.push_back(mkBtn(x, yb, bw, bh, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
    } else if (gScreen == SC_GAME) {
        GameLayout L = gameLayout();
        float gap = L.pad * 0.5f;
        float bw = (L.listW - 4 * gap) / 5;
        bool net = gM.mode == MODE_NET;
        bool over = gM.g.result != RES_NONE && !gM.g.moves.empty();
        const char *lb[5] = {over ? "РАЗБОР" : (net ? "НИЧЬЯ" : "ОТМЕНА"), "СДАТЬСЯ", "НОВАЯ", "ПОВОРОТ", "МЕНЮ"};
        int ids[5] = {over ? B_REVIEW : (net ? B_DRAW : B_UNDO), B_RESIGN, B_NEW, B_FLIP, B_MENU};
        int ic[5] = {over ? IC_SEARCH : (net ? IC_EQUAL : IC_UNDO), IC_FLAG, IC_PLUS, IC_FLIP, IC_MENU};
        int lts = L.tsSmall;
        for (int i = 0; i < 5; i++) lts = std::min(lts, fitScale(lb[i], bw * 0.9f, L.tsSmall));
        for (int i = 0; i < 5; i++) {
            Btn b = mkBtn(L.listX + i * (bw + gap), L.btnY, bw, L.btnH, ids[i], lb[i], ST_TOOL, lts);
            b.icon = ic[i];
            if (ids[i] == B_UNDO) b.enabled = canUndo();
            if (ids[i] == B_RESIGN) b.enabled = gM.g.result == RES_NONE && (!net || netConnected());
            if (ids[i] == B_DRAW) b.enabled = gM.g.result == RES_NONE && netConnected() && !gM.g.moves.empty();
            if (ids[i] == B_NEW && net) b.enabled = netConnected();
            gScreenBtns.push_back(b);
        }
        // кнопки просмотра ходов
        float ng = U * 2.0f;
        float nw = (L.listW - U * 6 - 4 * ng) / 5;
        int nid[5] = {B_NAV_FIRST, B_NAV_PREV, B_NAV_NEXT, B_NAV_LAST, B_ARROWS};
        int nic[5] = {IC_FIRST, IC_PREV, IC_NEXT, IC_LAST, IC_PENCIL};
        int vp = viewPly(), n = (int)gM.g.moves.size();
        for (int i = 0; i < 5; i++) {
            Btn b = mkBtn(L.listX + U * 3 + i * (nw + ng), L.navY, nw, L.navH, nid[i], "", ST_TOOL, lts);
            b.icon = nic[i];
            if (i < 4) b.enabled = i < 2 ? vp > 0 : vp < n;
            else b.selected = gArrowMode;
            gScreenBtns.push_back(b);
        }
    }
}

struct Panel {
    float x, y, w, h;
};
static Panel overlayPanel(float hFrac) {
    float U = uiU();
    Panel p;
    p.w = std::min(gW * 0.9f, U * 92.0f);
    p.h = std::min(gH * 0.8f, U * hFrac);
    p.x = (gW - p.w) * 0.5f;
    p.y = (gH - p.h) * 0.5f;
    return p;
}

static void buildOverlayButtons() {
    gOverBtns.clear();
    float U = uiU();
    int ts = uiTS();
    if (gOverlay == OV_CONFIRM) {
        Panel p = overlayPanel(52);
        float bw = (p.w - U * 12) / 2, bh = std::max(40.0f, U * 13.0f);
        float y = p.y + p.h - bh - U * 5;
        bool lostMsg = gConfirm == CF_NET_LOST;
        int yesStyle = (gConfirm == CF_NEW || gConfirm == CF_NET_DRAW || gConfirm == CF_NET_NEW || lostMsg) ? ST_PRIMARY : ST_DANGER;
        gOverBtns.push_back(mkBtn(p.x + U * 4, y, bw, bh, B_YES, lostMsg ? "В МЕНЮ" : "ДА", yesStyle, ts + 1));
        gOverBtns.push_back(mkBtn(p.x + p.w - U * 4 - bw, y, bw, bh, B_NO, lostMsg ? "ЗАКРЫТЬ" : "НЕТ", ST_NORMAL, ts + 1));
    } else if (gOverlay == OV_CHOOSE) {
        Panel p = overlayPanel(78);
        float bw = p.w - U * 10, bh = std::max(40.0f, U * 13.0f), gap = U * 2.5f;
        float x = p.x + U * 5;
        float y = p.y + p.h - U * 5 - 3 * bh - 2 * gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_ED_BOT, "С БОТОМ", ST_PRIMARY, ts + 1));
        y += bh + gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_ED_TWO, "ВДВОЁМ", ST_NORMAL, ts + 1));
        y += bh + gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_NO, "ОТМЕНА", ST_NORMAL, ts));
    } else if (gOverlay == OV_RESULT) {
        Panel p = overlayPanel(120);
        float bw = p.w - U * 10, bh = std::max(38.0f, U * 12.0f), gap = U * 2.2f;
        float x = p.x + U * 5;
        float y = p.y + p.h - U * 5 - 4 * bh - 3 * gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_RES_NEW, "НОВАЯ ПАРТИЯ", ST_PRIMARY, ts + 1));
        y += bh + gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_RES_REVIEW, "РАЗБОР ОШИБОК", ST_NORMAL, ts));
        y += bh + gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_RES_VIEW, "СМОТРЕТЬ ДОСКУ", ST_NORMAL, ts));
        y += bh + gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_RES_MENU, "В МЕНЮ", ST_NORMAL, ts));
    } else if (gOverlay == OV_PROMO) {
        Panel p = overlayPanel(50);
        float gap = U * 2.5f;
        float bw = (p.w - U * 8 - 3 * gap) / 4;
        float y = p.y + p.h - bw - U * 5;
        int types[4] = {eng::QUEEN, eng::ROOK, eng::BISHOP, eng::KNIGHT};
        int ids[4] = {B_PROMO_Q, B_PROMO_R, B_PROMO_B, B_PROMO_N};
        for (int i = 0; i < 4; i++) {
            Btn b = mkBtn(p.x + U * 4 + i * (bw + gap), y, bw, bw, ids[i], "", ST_SEG, ts);
            b.piece = eng::mkPiece(gM.g.cur.side, types[i]);
            gOverBtns.push_back(b);
        }
    }
}

// =====================================================================
//                            ОТРИСОВКА
// =====================================================================
static const Col COL_BG_TOP = C(28, 36, 50);
static const Col COL_BG_BOT = C(12, 15, 22);
static const Col COL_TEXT = C(240, 236, 226);
static const Col COL_DIM = C(150, 158, 172);
static const Col COL_GOLD = C(236, 186, 92);
static const Col COL_LIGHT = C(238, 216, 181);
static const Col COL_DARK = C(176, 132, 96);

static void drawBackground() {
    gVtx.clear();
    gIdx.clear();
    float W = (float)gW, H = (float)gH;
    gVtx.push_back(mkV(0, 0, COL_BG_TOP));
    gVtx.push_back(mkV(W, 0, COL_BG_TOP));
    gVtx.push_back(mkV(W, H, COL_BG_BOT));
    gVtx.push_back(mkV(0, H, COL_BG_BOT));
    int id[6] = {0, 1, 2, 0, 2, 3};
    SDL_RenderGeometry(R, nullptr, gVtx.data(), 4, id, 6);
}

static void drawPattern(float y0, float y1, int alpha) {
    float cs = std::max(16.0f, gW / 8.0f);
    for (int r = 0; r * cs < y1 - y0; r++)
        for (int c = 0; c < 9; c++) {
            if ((r + c) & 1) continue;
            float yy = y0 + r * cs;
            float t = (yy - y0) / std::max(1.0f, y1 - y0);
            int a = (int)(alpha * (1.0f - t));
            if (a <= 0) continue;
            fillRect(c * cs, yy, cs, std::min(cs, y1 - yy), C(255, 255, 255, a));
        }
}

static void drawIcon(int ic, float cx, float cy, float s, Col c) {
    float w = std::max(2.0f, s * 0.13f);
    switch (ic) {
        case IC_UNDO: {
            int n = 14;
            float r = s * 0.36f;
            float px = 0, py = 0;
            for (int i = 0; i <= n; i++) {
                float a = 3.1415926f * (-0.95f + 1.75f * i / n);
                float x = cx + std::cos(a) * r, y = cy + std::sin(a) * r + s * 0.05f;
                if (i) thickLine(px, py, x, y, w, c);
                px = x;
                py = y;
            }
            float ax = cx + std::cos(3.1415926f * -0.95f) * r, ay = cy + std::sin(3.1415926f * -0.95f) * r + s * 0.05f;
            Poly t;
            t.push_back(P(ax - s * 0.2f, ay - s * 0.02f));
            t.push_back(P(ax + s * 0.12f, ay - s * 0.16f));
            t.push_back(P(ax + s * 0.06f, ay + s * 0.18f));
            fillConvex(t, solid(c));
            break;
        }
        case IC_FLAG: {
            thickLine(cx - s * 0.28f, cy - s * 0.42f, cx - s * 0.28f, cy + s * 0.42f, w, c);
            Poly t;
            t.push_back(P(cx - s * 0.26f, cy - s * 0.40f));
            t.push_back(P(cx + s * 0.36f, cy - s * 0.20f));
            t.push_back(P(cx - s * 0.26f, cy + 0.02f * s));
            fillConvex(t, solid(c));
            break;
        }
        case IC_PLUS:
            thickLine(cx - s * 0.36f, cy, cx + s * 0.36f, cy, w * 1.2f, c);
            thickLine(cx, cy - s * 0.36f, cx, cy + s * 0.36f, w * 1.2f, c);
            break;
        case IC_FLIP: {
            float x1 = cx - s * 0.18f, x2 = cx + s * 0.18f;
            thickLine(x1, cy - s * 0.38f, x1, cy + s * 0.38f, w, c);
            thickLine(x2, cy - s * 0.38f, x2, cy + s * 0.38f, w, c);
            Poly a, b2;
            a.push_back(P(x1, cy - s * 0.48f));
            a.push_back(P(x1 + s * 0.17f, cy - s * 0.22f));
            a.push_back(P(x1 - s * 0.17f, cy - s * 0.22f));
            b2.push_back(P(x2, cy + s * 0.48f));
            b2.push_back(P(x2 - s * 0.17f, cy + s * 0.22f));
            b2.push_back(P(x2 + s * 0.17f, cy + s * 0.22f));
            fillConvex(a, solid(c));
            fillConvex(b2, solid(c));
            break;
        }
        case IC_MENU:
            for (int i = -1; i <= 1; i++) thickLine(cx - s * 0.34f, cy + i * s * 0.28f, cx + s * 0.34f, cy + i * s * 0.28f, w, c);
            break;
        case IC_FIRST: case IC_PREV: case IC_NEXT: case IC_LAST: {
            float dir = (ic == IC_FIRST || ic == IC_PREV) ? -1.0f : 1.0f;
            float h = s * 0.42f;
            Poly t;
            float tip = cx + dir * s * 0.30f, back = cx - dir * s * 0.22f;
            if (ic == IC_FIRST || ic == IC_LAST) { tip += dir * s * -0.08f; back += dir * s * -0.08f; }
            t.push_back(P(tip, cy));
            t.push_back(P(back, cy - h));
            t.push_back(P(back, cy + h));
            fillConvex(t, solid(c));
            if (ic == IC_FIRST || ic == IC_LAST) {
                float bx = tip + dir * s * 0.10f;
                thickLine(bx, cy - h, bx, cy + h, std::max(2.0f, s * 0.13f), c, false);
            }
            break;
        }
        case IC_PENCIL: {  // стрелка-указатель
            float x0 = cx - s * 0.32f, y0 = cy + s * 0.32f, x1 = cx + s * 0.30f, y1 = cy - s * 0.30f;
            thickLine(x0, y0, x1 - s * 0.10f, y1 + s * 0.10f, w * 1.1f, c);
            Poly t;
            t.push_back(P(x1 + s * 0.06f, y1 - s * 0.06f));
            t.push_back(P(x1 - s * 0.30f, y1 - s * 0.02f));
            t.push_back(P(x1 + s * 0.02f, y1 + s * 0.30f));
            fillConvex(t, solid(c));
            break;
        }
        case IC_ERASER: {  // ластик: наклонный брусок
            float a = 0.785f, ca = std::cos(a), sa = std::sin(a);
            float hw = s * 0.42f, hh = s * 0.20f;
            auto pt = [&](float u, float v) { return P(cx + u * ca - v * sa, cy + u * sa + v * ca); };
            Poly body;
            body.push_back(pt(-hw, -hh));
            body.push_back(pt(hw, -hh));
            body.push_back(pt(hw, hh));
            body.push_back(pt(-hw, hh));
            fillConvex(body, solid(c));
            Poly tip;
            tip.push_back(pt(-hw, -hh));
            tip.push_back(pt(-hw * 0.15f, -hh));
            tip.push_back(pt(-hw * 0.15f, hh));
            tip.push_back(pt(-hw, hh));
            fillConvex(tip, solid(C(236, 120, 110)));
            break;
        }
        case IC_SEARCH: {
            float r = s * 0.26f;
            ringShape(cx - s * 0.08f, cy - s * 0.08f, r - w * 0.5f, r + w * 0.5f, c);
            thickLine(cx + s * 0.12f, cy + s * 0.12f, cx + s * 0.38f, cy + s * 0.38f, w * 1.3f, c);
            break;
        }
        case IC_EQUAL:
            thickLine(cx - s * 0.34f, cy - s * 0.17f, cx + s * 0.34f, cy - s * 0.17f, w * 1.2f, c);
            thickLine(cx - s * 0.34f, cy + s * 0.17f, cx + s * 0.34f, cy + s * 0.17f, w * 1.2f, c);
            break;
        default: break;
    }
}

static void drawButton(const Btn &b, bool pressed) {
    float rad = std::min(b.r.h * 0.28f, uiU() * 3.0f);
    Col top, bot, border, tc = COL_TEXT;
    switch (b.style) {
        case ST_PRIMARY: top = C(242, 196, 104); bot = C(196, 136, 52); border = C(255, 226, 160); tc = C(48, 30, 10); break;
        case ST_DANGER: top = C(196, 82, 72); bot = C(146, 48, 44); border = C(230, 130, 118); break;
        case ST_SEG:
            if (b.selected) { top = C(242, 196, 104); bot = C(196, 136, 52); border = C(255, 230, 170); tc = C(48, 30, 10); }
            else { top = C(58, 70, 90); bot = C(42, 52, 68); border = C(84, 98, 122); }
            break;
        case ST_TOOL:
            if (b.selected) { top = C(70, 170, 80); bot = C(40, 128, 52); border = C(150, 230, 150); }
            else { top = C(52, 63, 82); bot = C(38, 47, 62); border = C(76, 90, 114); }
            break;
        default: top = C(66, 80, 102); bot = C(46, 57, 75); border = C(96, 112, 138); break;
    }
    if (pressed) { top = mix(top, C(0, 0, 0), 0.25f); bot = mix(bot, C(0, 0, 0), 0.25f); }
    if (!b.enabled) { top = mix(top, C(30, 34, 42), 0.6f); bot = mix(bot, C(30, 34, 42), 0.6f); border = mix(border, C(30, 34, 42), 0.6f); tc = C(110, 114, 124); }
    float off = pressed ? 1.0f : 0.0f;
    fillRRect(b.r.x, b.r.y + std::max(2.0f, uiU() * 0.6f), b.r.w, b.r.h, rad, C(0, 0, 0, 90));
    fillRRect(b.r.x, b.r.y + off, b.r.w, b.r.h, rad, border);
    float bw = std::max(1.0f, uiU() * 0.35f);
    fillRRect(b.r.x + bw, b.r.y + bw + off, b.r.w - 2 * bw, b.r.h - 2 * bw, rad - bw, vgrad(top, bot, b.r.y, b.r.y + b.r.h));
    float cx = b.r.x + b.r.w * 0.5f;
    if (b.style == ST_TOOL && b.label.empty()) {
        drawIcon(b.icon, cx, b.r.y + b.r.h * 0.5f + off, b.r.h * 0.42f, tc);
        return;
    }
    if (b.style == ST_TOOL) {
        float is = b.r.h * 0.36f;
        drawIcon(b.icon, cx, b.r.y + b.r.h * 0.36f + off, is, tc);
        text(b.label, cx, b.r.y + b.r.h * 0.70f + off, b.ts, tc, 1, false);
        return;
    }
    if (b.piece > 0 && b.label.empty()) {
        float ps = std::min(b.r.h, b.r.w) * 0.86f;
        drawPiece(b.piece, cx - ps * 0.5f, b.r.y + (b.r.h - ps) * 0.5f + off, ps);
        return;
    }
    if (b.piece > 0) {
        float ps = std::min(b.r.h * 0.62f, b.r.w * 0.6f);
        drawPiece(b.piece, cx - ps * 0.5f, b.r.y + b.r.h * 0.06f + off, ps);
        int sc = fitScale(b.label, b.r.w * 0.9f, b.ts);
        if (!b.label.empty()) text(b.label, cx, b.r.y + b.r.h * 0.94f - textH(sc) + off, sc, tc, 1, false);
        return;
    }
    if (b.piece < 0) {
        float ps = std::min(b.r.h * 0.62f, b.r.w * 0.45f);
        drawPiece(eng::mkPiece(eng::WHITE, eng::KING), cx - ps * 0.85f, b.r.y + b.r.h * 0.06f + off, ps);
        drawPiece(eng::mkPiece(eng::BLACK, eng::KING), cx - ps * 0.15f, b.r.y + b.r.h * 0.06f + off, ps);
        int sc = fitScale(b.label, b.r.w * 0.9f, b.ts);
        text(b.label, cx, b.r.y + b.r.h * 0.94f - textH(sc) + off, sc, tc, 1, false);
        return;
    }
    int sc = fitScale(b.label, b.r.w * 0.88f, b.ts);
    text(b.label, cx, b.r.y + (b.r.h - textH(sc)) * 0.5f + off, sc, tc, 1, b.style != ST_PRIMARY && !(b.style == ST_SEG && b.selected));
}

static void drawButtons(const std::vector<Btn> &v, bool interactive) {
    for (auto &b : v) drawButton(b, interactive && gPressed == b.id && gPtr.down && inRect(b.r, gPtr.x, gPtr.y));
}

// ---------- меню ----------
static void drawMenu() {
    drawBackground();
    float W = (float)gW, H = (float)gH, U = uiU();
    drawPattern(H * 0.62f, (float)gH, 10);
    MenuM mm = menuMetrics();
    float ps = mm.ps;
    float cy = mm.oy;
    radial(W * 0.5f, cy + ps * 0.55f, ps * 1.3f, C(236, 186, 92, 60), C(236, 186, 92, 0));
    drawPiece(eng::mkPiece(eng::BLACK, eng::QUEEN), W * 0.5f - ps * 0.08f, cy + ps * 0.08f, ps * 0.92f);
    drawPiece(eng::mkPiece(eng::WHITE, eng::KING), W * 0.5f - ps * 0.88f, cy, ps);
    int tts = mm.tts;
    float ty = mm.ty;
    text("ШАХМАТЫ", W * 0.5f, ty, tts, COL_GOLD, 1, true);
    int sts = mm.sts;
    std::string sub = "ПОБЕД " + std::to_string(gStats.wins) + " · ПОРАЖЕНИЙ " + std::to_string(gStats.losses) +
                      " · НИЧЬИХ " + std::to_string(gStats.draws);
    sts = fitScale(sub, W * 0.9f, sts);
    text(sub, W * 0.5f, ty + textH(tts) + U * 3, sts, COL_DIM, 1, false);
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

// ---------- настройки ----------
static void drawSetup() {
    drawBackground();
    float W = (float)gW, H = (float)gH, U = uiU();
    int ts = uiTS();
    float top = H * 0.05f;
    int tts = std::max(2, ts * 2);
    std::string title = gSetupMode == MODE_BOT ? "ИГРА С БОТОМ" : "ИГРА ВДВОЁМ";
    tts = fitScale(title, W * 0.9f, tts);
    text(title, W * 0.5f, top + U * 6, tts, COL_GOLD, 1);
    {
        std::string sub = !gCustomFen.empty() ? "СВОЯ РАССТАНОВКА ФИГУР" : (gSetupMode == MODE_TWO ? "ДОСКА ПОВОРАЧИВАЕТСЯ ПОСЛЕ ХОДА" : "");
        if (!sub.empty()) {
            int s2 = fitScale(sub, W * 0.9f, ts);
            text(sub, W * 0.5f, top + U * 6 + textH(tts) + U * 3, s2, gCustomFen.empty() ? COL_DIM : C(140, 196, 255), 1, false);
        }
    }
    float bw = std::min(W * 0.9f, U * 90.0f), x = (W - bw) * 0.5f;
    float bh = std::max(36.0f, U * 12.5f);
    float y = H * 0.05f + U * 26.0f;
    if (gSetupMode == MODE_BOT) {
        text("СЛОЖНОСТЬ", x, y, ts, COL_TEXT);
        y += textH(ts) + U * 3 + bh + U * 3;
        text(LEVEL_NAME[gSet.level], W * 0.5f, y, ts, COL_GOLD, 1);
        y += textH(ts) + U * 7;
        text("ВАШ ЦВЕТ", x, y, ts, COL_TEXT);
        y += textH(ts) + U * 3 + bh * 1.35f + U * 7;
    }
    text("ЧАСЫ (НА КАЖДОГО)", x, y, ts, COL_TEXT);
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

// ---------- статистика ----------
static void drawStats() {
    drawBackground();
    float W = (float)gW, H = (float)gH, U = uiU();
    int ts = uiTS();
    float top = H * 0.05f;
    text("СТАТИСТИКА", W * 0.5f, top + U * 6, std::max(2, ts * 2), COL_GOLD, 1);
    float pw = std::min(W * 0.86f, U * 86.0f), px = (W - pw) * 0.5f;
    float py = top + U * 6 + textH(ts * 2) + U * 8;
    float lh = textH(ts + 1) + U * 6;
    int total = gStats.wins + gStats.losses + gStats.draws;
    int pct = total ? (int)std::lround(100.0 * (gStats.wins + 0.5 * gStats.draws) / total) : 0;
    struct Row { const char *l; std::string v; Col c; };
    std::string netv = std::to_string(gStats.netW) + "-" + std::to_string(gStats.netL) + "-" + std::to_string(gStats.netD);
    Row rows[7] = {
        {"ПОБЕДЫ", std::to_string(gStats.wins), C(120, 214, 120)},
        {"ПОРАЖЕНИЯ", std::to_string(gStats.losses), C(232, 110, 100)},
        {"НИЧЬИ", std::to_string(gStats.draws), C(200, 200, 210)},
        {"ВСЕГО С БОТОМ", std::to_string(total), COL_TEXT},
        {"РЕЗУЛЬТАТ", std::to_string(pct) + "%", COL_GOLD},
        {"ПАРТИЙ ВДВОЁМ", std::to_string(gStats.two), COL_TEXT},
        {"ПО СЕТИ (В-П-Н)", netv, COL_TEXT},
    };
    float ph = lh * 7 + U * 6;
    fillRRect(px, py, pw, ph, U * 3, C(36, 46, 62, 230));
    float y = py + U * 3 + (lh - textH(ts + 1)) * 0.5f;
    for (int i = 0; i < 7; i++) {
        int sc = fitScale(rows[i].l, pw * 0.6f, ts + 1);
        text(rows[i].l, px + U * 4, y, sc, COL_DIM, 0, false);
        text(rows[i].v, px + pw - U * 4, y, ts + 1, rows[i].c, 2);
        if (i < 6) fillRect(px + U * 4, y + lh - (lh - textH(ts + 1)) * 0.5f - 1, pw - U * 8, 1, C(255, 255, 255, 18));
        y += lh;
    }
    // полоска соотношения
    if (total > 0) {
        float by = py + ph + U * 5, bh = U * 3, bwid = pw;
        float w1 = bwid * gStats.wins / total, w2 = bwid * gStats.draws / total;
        fillRRect(px, by, bwid, bh, bh * 0.5f, C(232, 110, 100));
        fillRect(px + w1, by, w2, bh, C(190, 190, 200));
        if (gStats.wins > 0) fillRRect(px, by, std::max(bh, w1), bh, bh * 0.5f, C(120, 214, 120));
    }
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

// ---------- партия ----------
static std::string fmtClock(long long ms) {
    if (ms < 0) ms = 0;
    char b[32];
    if (ms < 20000) {
        int t = (int)(ms / 100);
        snprintf(b, sizeof b, "%d.%d", t / 10, t % 10);
    } else {
        int s = (int)((ms + 999) / 1000);
        snprintf(b, sizeof b, "%d:%02d", s / 60, s % 60);
    }
    return b;
}

static void capturedInfo(int color, std::vector<int> &capt, int &adv) {
    // capt — фигуры противника, которые съел color; adv — перевес в пешках
    static const int START[7] = {0, 8, 2, 2, 2, 1, 1};
    static const int PV[7] = {0, 1, 3, 3, 5, 9, 0};
    int cnt[2][7] = {{0}}, st[2][7] = {{0}};
    const eng::Board &b = gM.g.cur;
    for (int s = 0; s < 64; s++)
        if (b.sq[s]) cnt[eng::pColor(b.sq[s])][eng::pType(b.sq[s])]++;
    // считаем от позиции, с которой началась партия (своя расстановка — своя точка отсчёта)
    const eng::Board *sb = gM.g.startFen.empty() ? nullptr : (gM.g.before.empty() ? &gM.g.cur : &gM.g.before[0]);
    for (int c = 0; c < 2; c++)
        for (int t = 0; t < 7; t++) st[c][t] = START[t];
    if (sb) {
        memset(st, 0, sizeof(st));
        for (int s = 0; s < 64; s++)
            if (sb->sq[s]) st[eng::pColor(sb->sq[s])][eng::pType(sb->sq[s])]++;
    }
    int opp = color ^ 1;
    capt.clear();
    for (int t = eng::QUEEN; t >= eng::PAWN; t--) {
        int miss = st[opp][t] - cnt[opp][t];
        for (int i = 0; i < miss; i++) capt.push_back(eng::mkPiece(opp, t));
    }
    int m[2] = {0, 0};
    for (int c = 0; c < 2; c++)
        for (int t = 1; t <= 5; t++) m[c] += cnt[c][t] * PV[t];
    adv = m[color] - m[opp];
}

static std::string sideName(int c, bool nominative) {
    if (nominative) return c == eng::WHITE ? "БЕЛЫЕ" : "ЧЁРНЫЕ";
    return c == eng::WHITE ? "БЕЛЫХ" : "ЧЁРНЫХ";
}

static void drawPlayerBar(const GameLayout &L, float y, int color) {
    float x = L.listX, w = L.listW, h = L.barH, U = uiU();
    bool toMove = gM.g.result == RES_NONE && gM.g.cur.side == color;
    fillRRect(x, y, w, h, U * 2.2f, toMove ? C(48, 60, 80, 235) : C(30, 38, 52, 200));
    if (toMove) fillRRect(x, y + h * 0.18f, U * 1.0f, h * 0.64f, U * 0.5f, COL_GOLD);
    float r = h * 0.2f;
    float cx = x + U * 3.5f + r, cy = y + h * 0.5f;
    fillCircle(cx, cy, r + std::max(1.0f, U * 0.35f), color == eng::WHITE ? C(30, 26, 22) : C(170, 170, 176));
    fillCircle(cx, cy, r, color == eng::WHITE ? C(246, 240, 228) : C(28, 28, 32));
    std::string name;
    if (gM.mode == MODE_BOT) {
        if (color == gM.human) name = "ВЫ";
        else name = "БОТ · " + std::string(LEVEL_NAME[gM.level]);
    } else if (gM.mode == MODE_NET) {
        name = color == gM.human ? "ВЫ" : "СОПЕРНИК";
    } else {
        name = sideName(color, true);
    }
    int ts = L.ts;
    float clockW = gM.clockInit > 0 ? std::max(U * 22.0f, (float)textW("00:00", ts + 1) + U * 5) : 0;
    float nx = cx + r + U * 3;
    float availName = w - (nx - x) - clockW - U * 4;
    int nts = fitScale(name, availName * 0.62f, ts);
    float ty = y + h * 0.5f - textH(nts) * (gM.mode == MODE_BOT || true ? 0.95f : 0.5f);
    text(name, nx, ty, nts, COL_TEXT);
    if (gM.mode == MODE_BOT && color != gM.human && botThinking()) {
        float dx = nx + textW(name, nts) + U * 3;
        Uint32 t = SDL_GetTicks();
        for (int i = 0; i < 3; i++) {
            float ph = std::sin((t / 160.0f) - i * 0.9f) * 0.5f + 0.5f;
            fillCircle(dx + i * U * 2.4f, ty + textH(nts) * 0.5f, U * (0.5f + 0.45f * ph), withA(COL_GOLD, (int)(120 + 135 * ph)));
        }
    }
    // съеденные фигуры
    std::vector<int> capt;
    int adv;
    capturedInfo(color, capt, adv);
    float ps = std::min(h * 0.42f, U * 5.5f);
    float px = nx, py = y + h * 0.53f;
    float maxX = x + w - clockW - U * 4 - textW("+99", L.tsSmall);
    int prev = -1;
    for (int p : capt) {
        if (px + ps > maxX) break;
        if (prev >= 0 && prev != p) px += ps * 0.25f;
        drawPiece(p, px, py, ps);
        px += ps * 0.55f;
        prev = p;
    }
    if (adv > 0) text("+" + std::to_string(adv), px + ps * 0.55f, py + (ps - textH(L.tsSmall)) * 0.5f, L.tsSmall, COL_DIM, 0, false);
    // часы
    if (gM.clockInit > 0) {
        long long ms = gM.tLeft[color];
        float cw = clockW, ch = h * 0.7f;
        float kx = x + w - cw - U * 2, ky = y + (h - ch) * 0.5f;
        bool low = ms < 30000;
        Col bg = toMove ? (low ? C(214, 76, 64) : C(236, 230, 214)) : C(22, 28, 38);
        Col fg = toMove ? (low ? C(255, 255, 255) : C(30, 30, 30)) : (low ? C(232, 120, 110) : COL_DIM);
        fillRRect(kx, ky, cw, ch, U * 1.6f, bg);
        std::string s = fmtClock(ms);
        int cts = fitScale(s, cw * 0.86f, ts + 1);
        text(s, kx + cw * 0.5f, ky + (ch - textH(cts)) * 0.5f, cts, fg, 1, false);
    }
}

static float animT() {
    if (gAnims.empty()) return 1.0f;
    float t = (SDL_GetTicks() - gAnimStart) / (float)ANIM_MS;
    if (t >= 1) return 1.0f;
    return 1 - (1 - t) * (1 - t) * (1 - t);
}

static void drawArrow(float x1, float y1, float x2, float y2, float w, Col c) {
    float dx = x2 - x1, dy = y2 - y1;
    float L = std::sqrt(dx * dx + dy * dy);
    if (L < 1) return;
    float ux = dx / L, uy = dy / L;
    float head = w * 2.4f;
    float hx = x2 - ux * head, hy = y2 - uy * head;
    thickLine(x1, y1, hx, hy, w, c, false);
    Poly t;
    t.push_back(P(x2, y2));
    t.push_back(P(hx - uy * w * 1.5f, hy + ux * w * 1.5f));
    t.push_back(P(hx + uy * w * 1.5f, hy - ux * w * 1.5f));
    fillConvex(t, solid(c));
}

static void drawBoard(const GameLayout &L) {
    float U = uiU();
    float fr = std::max(3.0f, L.cell * 0.09f);
    fillRRect(L.bx - fr, L.by - fr, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, C(0, 0, 0, 90));
    fillRRect(L.bx - fr, L.by - fr + 1, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, vgrad(C(96, 66, 42), C(58, 38, 24), L.by, L.by + L.S));
    const eng::Board &b = viewBoard();
    for (int s = 0; s < 64; s++) {
        float x, y;
        sqToXY(L, s, x, y);
        bool light = ((s & 7) + (s >> 3)) & 1;
        Col c = light ? COL_LIGHT : COL_DARK;
        fillRect(x, y, L.cell, L.cell, c);
    }
    // последний ход (или ход, на котором остановлен просмотр)
    if (viewPly() > 0) {
        eng::Move m = gM.g.moves[(size_t)viewPly() - 1];
        float x, y;
        sqToXY(L, eng::mFrom(m), x, y);
        fillRect(x, y, L.cell, L.cell, C(246, 222, 60, 95));
        sqToXY(L, eng::mTo(m), x, y);
        fillRect(x, y, L.cell, L.cell, C(246, 222, 60, 125));
    }
    if (gSel >= 0) {
        float x, y;
        sqToXY(L, gSel, x, y);
        fillRect(x, y, L.cell, L.cell, C(92, 178, 92, 150));
    }
    // король под шахом
    if (b.inCheck(b.side)) {
        float x, y;
        sqToXY(L, b.kingSq[b.side], x, y);
        radial(x + L.cell * 0.5f, y + L.cell * 0.5f, L.cell * 0.62f, C(255, 30, 20, 230), C(255, 30, 20, 0));
    }
    // координаты
    int cs = std::max(1, (int)(L.cell / 30.0f));
    for (int i = 0; i < 8; i++) {
        int file = whiteBottom() ? i : 7 - i;
        int rank = whiteBottom() ? 7 - i : i;
        std::string fs(1, (char)('a' + file)), rs(1, (char)('1' + rank));
        float x = L.bx + i * L.cell, y = L.by + 7 * L.cell;
        bool lightF = ((file + (whiteBottom() ? 0 : 7)) & 1) != 0;
        text(fs, x + L.cell - textW(fs, cs) - cs * 1.5f, y + L.cell - textH(cs) - cs * 1.2f, cs,
             lightF ? COL_DARK : COL_LIGHT, 0, false);
        float yy = L.by + i * L.cell;
        bool lightR = ((rank + (whiteBottom() ? 0 : 7)) & 1) != 0;
        text(rs, L.bx + cs * 1.5f, yy + cs * 1.2f, cs, lightR ? COL_DARK : COL_LIGHT, 0, false);
    }
    // фигуры
    float at = animT();
    bool animating = at < 1.0f && !viewing();
    for (int s = 0; s < 64; s++) {
        if (!b.sq[s]) continue;
        if (gDrag.active && gDrag.started && s == gDrag.sq) continue;
        bool hidden = false;
        if (animating)
            for (auto &a : gAnims)
                if (a.to == s) hidden = true;
        if (hidden) continue;
        float x, y;
        sqToXY(L, s, x, y);
        drawPiece(b.sq[s], x, y, L.cell);
    }
    if (animating) {
        for (auto &a : gAnims) {
            float x0, y0, x1, y1;
            sqToXY(L, a.from, x0, y0);
            sqToXY(L, a.to, x1, y1);
            drawPiece(a.piece, x0 + (x1 - x0) * at, y0 + (y1 - y0) * at, L.cell);
        }
    }
    // возможные ходы
    for (auto m : gTargets) {
        int t = eng::mTo(m);
        float x, y;
        sqToXY(L, t, x, y);
        float cx = x + L.cell * 0.5f, cy = y + L.cell * 0.5f;
        if (b.sq[t] || (eng::mFlags(m) & eng::F_EP)) ringShape(cx, cy, L.cell * 0.40f, L.cell * 0.49f, C(20, 60, 20, 95));
        else fillCircle(cx, cy, L.cell * 0.16f, C(20, 60, 20, 90));
    }
    // свои стрелки и кружки
    {
        Col ac = C(21, 140, 40, 175);
        float aw = std::max(3.0f, L.cell * 0.17f);
        for (int c : gUCircles) {
            float x, y;
            sqToXY(L, c, x, y);
            ringShape(x + L.cell * 0.5f, y + L.cell * 0.5f, L.cell * 0.42f, L.cell * 0.49f, ac);
        }
        auto arrowSq = [&](int a, int b2, Col col) {
            float x0, y0, x1, y1;
            sqToXY(L, a, x0, y0);
            sqToXY(L, b2, x1, y1);
            float cx0 = x0 + L.cell * 0.5f, cy0 = y0 + L.cell * 0.5f, cx1 = x1 + L.cell * 0.5f, cy1 = y1 + L.cell * 0.5f;
            float dx = cx1 - cx0, dy = cy1 - cy0, len = std::sqrt(dx * dx + dy * dy);
            if (len < 1) return;
            float off = L.cell * 0.18f;  // начинаем чуть от центра клетки
            drawArrow(cx0 + dx / len * off, cy0 + dy / len * off, cx1, cy1, aw, col);
        };
        for (auto &u : gUArrows) arrowSq(u.a, u.b, ac);
        if (gArrowDrag && gArrowFrom >= 0) {
            int hs = xyToSq(L, gPtr.x, gPtr.y);
            if (hs >= 0 && hs != gArrowFrom) arrowSq(gArrowFrom, hs, C(21, 140, 40, 120));
        }
    }
    // перетаскивание
    if (gDrag.active && gDrag.started && gSel >= 0) {
        int hs = xyToSq(L, gPtr.x, gPtr.y);
        if (hs >= 0) {
            float x, y;
            sqToXY(L, hs, x, y);
            float w = std::max(2.0f, L.cell * 0.06f);
            Col hc = isTarget(hs) ? C(255, 255, 255, 170) : C(255, 255, 255, 60);
            fillRect(x, y, L.cell, w, hc);
            fillRect(x, y + L.cell - w, L.cell, w, hc);
            fillRect(x, y, w, L.cell, hc);
            fillRect(x + L.cell - w, y, w, L.cell, hc);
        }
        float ds = L.cell * 1.35f;
        drawPiece(b.sq[gSel], gPtr.x - ds * 0.5f, gPtr.y - ds * 0.85f, ds);
    }
    (void)U;
}

static std::string statusText(Col &c) {
    c = COL_TEXT;
    const Game &g = gM.g;
    if (viewing()) {
        c = C(140, 196, 255);
        if (gViewPly == 0) return "ПРОСМОТР: НАЧАЛО ПАРТИИ";
        int i = gViewPly - 1;
        int p = i + g.off();
        return "ПРОСМОТР: " + std::to_string(p / 2 + 1) + (p % 2 ? "... " : ". ") + g.san[(size_t)i];
    }
    if (g.result != RES_NONE) {
        c = COL_GOLD;
        if (g.result == RES_DRAW) return "НИЧЬЯ";
        int win = g.result == RES_WHITE ? eng::WHITE : eng::BLACK;
        if (gM.mode != MODE_TWO) return win == gM.human ? "ВЫ ПОБЕДИЛИ!" : "ВЫ ПРОИГРАЛИ";
        return "ПОБЕДИЛИ " + sideName(win, true);
    }
    bool chk = g.cur.inCheck(g.cur.side);
    std::string s;
    if (gM.mode == MODE_NET) {
        if (!netConnected()) {
            c = C(255, 120, 100);
            return "НЕТ СВЯЗИ С СОПЕРНИКОМ";
        }
        s = g.cur.side == gM.human ? "ВАШ ХОД" : "ХОД СОПЕРНИКА";
    } else if (gM.mode == MODE_BOT) {
        if (g.cur.side == gM.human) s = "ВАШ ХОД";
        else {
            int dots = (SDL_GetTicks() / 350) % 4;
            s = "БОТ ДУМАЕТ" + std::string((size_t)dots, '.');
        }
    } else {
        s = "ХОД " + sideName(g.cur.side, false);
    }
    if (chk) {
        c = C(255, 120, 100);
        s = "ШАХ! " + s;
    }
    return s;
}

struct ListGeo {
    float y0, lineH, numW, plyW, colW, sy;
    int lts, sts, rowsVis, cols, totalRows, firstRow, nPairs;
};
static ListGeo listGeo(const GameLayout &L, const std::string &st) {
    ListGeo G;
    float U = uiU();
    G.sy = L.listY + U * 2.2f;
    G.sts = fitScale(st, L.listW - U * 6, L.ts);
    G.y0 = G.sy + textH(G.sts) + U * 2.5f;
    G.lts = L.tsSmall;
    G.lineH = textH(G.lts) + U * 2.2f;
    G.rowsVis = std::max(0, (int)((L.navY - U * 1.2f - G.y0) / G.lineH));
    G.nPairs = (int)(gM.g.san.size() + gM.g.off() + 1) / 2;
    G.numW = (float)textW("000.", G.lts);
    G.plyW = (float)textW("Крxe8+ ", G.lts);
    float pairW = G.numW + 2 * G.plyW + U * 3;
    G.cols = std::max(1, (int)((L.listW - U * 4) / pairW));
    G.totalRows = (G.nPairs + G.cols - 1) / G.cols;
    int maxScroll = std::max(0, G.totalRows - G.rowsVis);
    // держим выбранный ход в поле зрения
    int hl = viewPly() - 1;
    if (gListFollow && hl >= 0 && G.rowsVis > 0) {
        int row = ((hl + gM.g.off()) / 2) / G.cols;
        int first = std::max(0, G.totalRows - G.rowsVis - gListScroll);
        if (row < first) gListScroll = G.totalRows - G.rowsVis - row;
        else if (row >= first + G.rowsVis) gListScroll = G.totalRows - row - 1;
    }
    if (!viewing() && gListFollow) gListScroll = 0;
    gListFollow = false;
    if (gListScroll > maxScroll) gListScroll = maxScroll;
    if (gListScroll < 0) gListScroll = 0;
    G.firstRow = std::max(0, G.totalRows - G.rowsVis - gListScroll);
    G.colW = (L.listW - U * 4) / G.cols;
    return G;
}

// Какой ход в списке под пальцем (-1 — никакой)
static int listHit(const GameLayout &L, float x, float y) {
    Col c;
    ListGeo G = listGeo(L, statusText(c));
    float U = uiU();
    if (y < G.y0 - U || G.rowsVis <= 0) return -1;
    int r = (int)std::floor((y - G.y0 + U) / G.lineH);
    if (r < 0 || r >= G.rowsVis) return -1;
    int row = G.firstRow + r;
    int col = (int)std::floor((x - L.listX - U * 2.5f) / G.colW);
    if (col < 0 || col >= G.cols) return -1;
    int pi = row * G.cols + col;
    if (pi >= G.nPairs) return -1;
    float cx = L.listX + U * 2.5f + col * G.colW + G.numW + U * 1.5f;
    int k = x < cx + G.plyW ? 0 : 1;
    int ply = pi * 2 + k - gM.g.off();
    if (ply < 0) ply = 0;
    if (ply >= (int)gM.g.san.size()) ply = (int)gM.g.san.size() - 1;
    return ply;
}

static void drawMoveList(const GameLayout &L) {
    float U = uiU();
    fillRRect(L.listX, L.listY, L.listW, L.listH, U * 2.2f, C(22, 28, 40, 220));
    Col sc;
    std::string st = statusText(sc);
    ListGeo G = listGeo(L, st);
    text(st, L.listX + U * 3, G.sy, G.sts, sc);
    std::string cnt = gM.g.moves.empty() ? "" : ("ХОД " + std::to_string((gM.g.moves.size() + gM.g.off() + 1) / 2));
    if (!cnt.empty() && textW(st, G.sts) + textW(cnt, L.tsSmall) + U * 10 < L.listW)
        text(cnt, L.listX + L.listW - U * 3, G.sy + textH(G.sts) - textH(L.tsSmall), L.tsSmall, COL_DIM, 2, false);
    fillRect(L.listX + U * 3, G.y0 - U * 1.2f, L.listW - U * 6, 1, C(255, 255, 255, 25));
    int lts = G.lts;
    int hl = viewPly() - 1;  // подсвеченный ход
    for (int r = 0; r < G.rowsVis; r++) {
        int row = G.firstRow + r;
        if (row >= G.totalRows) break;
        for (int c = 0; c < G.cols; c++) {
            int pi = row * G.cols + c;
            if (pi >= G.nPairs) break;
            float x = L.listX + U * 2.5f + c * G.colW;
            float y = G.y0 + r * G.lineH;
            std::string num = std::to_string(pi + 1) + ".";
            text(num, x + G.numW - textW(num, lts), y, lts, COL_DIM, 0, false);
            for (int k = 0; k < 2; k++) {
                int ply = pi * 2 + k - gM.g.off();
                float mx = x + G.numW + U * 1.5f + k * G.plyW;
                if (ply < 0) {
                    text("...", mx, y, lts, COL_DIM, 0, false);
                    continue;
                }
                if (ply >= (int)gM.g.san.size()) break;
                bool h = ply == hl;
                Col hc = viewing() ? C(140, 196, 255, 80) : C(236, 186, 92, 70);
                if (h) fillRRect(mx - U * 0.8f, y - U * 0.8f, textW(gM.g.san[ply], lts) + U * 1.6f, textH(lts) + U * 1.6f, U * 0.8f, hc);
                Col tc = h ? (viewing() ? C(170, 214, 255) : COL_GOLD) : (viewing() && ply > hl ? C(120, 126, 140) : COL_TEXT);
                text(gM.g.san[ply], mx, y, lts, tc, 0, false);
            }
        }
    }
    int maxScroll = std::max(0, G.totalRows - G.rowsVis);
    if (maxScroll > 0 && G.rowsVis > 0) {
        float trackH = G.rowsVis * G.lineH;
        float th = std::max(U * 4, trackH * G.rowsVis / G.totalRows);
        float tpos = (float)(maxScroll - gListScroll) / maxScroll;
        fillRRect(L.listX + L.listW - U * 1.6f, G.y0 + (trackH - th) * tpos, U * 0.8f, th, U * 0.4f, C(255, 255, 255, 60));
    }
}

static void drawGame() {
    drawBackground();
    GameLayout L = gameLayout();
    ensurePieceTex((int)L.cell);
    bool wb = whiteBottom();
    drawPlayerBar(L, L.topBarY, wb ? eng::BLACK : eng::WHITE);
    drawPlayerBar(L, L.botBarY, wb ? eng::WHITE : eng::BLACK);
    drawMoveList(L);
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
    drawBoard(L);
}

// ---------- обучение ----------
static std::vector<std::string> wrapText(const std::string &s, int sc, float maxW) {
    std::vector<std::string> out;
    size_t pos = 0;
    while (pos <= s.size()) {
        size_t e = s.find('\n', pos);
        if (e == std::string::npos) e = s.size();
        std::string para = s.substr(pos, e - pos);
        std::string cur;
        size_t i = 0;
        while (i < para.size()) {
            while (i < para.size() && para[i] == ' ') i++;
            size_t j = i;
            while (j < para.size() && para[j] != ' ') j++;
            if (j > i) {
                std::string w = para.substr(i, j - i);
                std::string test = cur.empty() ? w : cur + " " + w;
                if (cur.empty() || textW(test, sc) <= maxW) cur = test;
                else {
                    out.push_back(cur);
                    cur = w;
                }
            }
            i = j;
        }
        out.push_back(cur);
        pos = e + 1;
    }
    return out;
}

static void lessonSqXY(const LessonLayout &L, int s, float &x, float &y) {
    int f = s & 7, r = s >> 3;
    int col = gLWB ? f : 7 - f, row = gLWB ? 7 - r : r;
    x = L.bx + col * L.cell;
    y = L.by + row * L.cell;
}
static int lessonXYToSq(const LessonLayout &L, float x, float y) {
    if (x < L.bx || y < L.by || x >= L.bx + L.S || y >= L.by + L.S) return -1;
    int col = (int)((x - L.bx) / L.cell), row = (int)((y - L.by) / L.cell);
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return gLWB ? (7 - row) * 8 + col : row * 8 + (7 - col);
}

static float gLScroll = 0, gLScrollStart = 0;
static bool gLessonDrag = false;

static void drawLearn() {
    drawBackground();
    float W = (float)gW, H = (float)gH, U = uiU();
    int ts = uiTS();
    float top = H * 0.05f;
    int tts = fitScale("ОБУЧЕНИЕ", W * 0.9f, ts * 2);
    text("ОБУЧЕНИЕ", W * 0.5f, top + U * 6, tts, COL_GOLD, 1);
    int sts = fitScale("ПРАВИЛА, СТРАТЕГИЯ И ЗАДАЧИ", W * 0.9f, std::max(1, ts - 1));
    text("ПРАВИЛА, СТРАТЕГИЯ И ЗАДАЧИ", W * 0.5f, top + U * 6 + textH(tts) + U * 3, sts, COL_DIM, 1, false);
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
    for (auto &b : gScreenBtns) {
        if (b.id < B_CH0 || b.id >= B_CH0 + NCHAP) continue;
        int i = b.id - B_CH0;
        bool pressed = gPressed == b.id && gPtr.down && inRect(b.r, gPtr.x, gPtr.y);
        float off = pressed ? 1.0f : 0.0f;
        float r = std::min(b.r.h * 0.3f, U * 4.5f);
        float cx = b.r.x + U * 3 + r, cy = b.r.y + b.r.h * 0.5f + off;
        fillCircle(cx, cy, r, C(236, 186, 92));
        std::string num = std::to_string(i + 1);
        int ns = std::max(1, (int)(r * 1.1f / 7));
        text(num, cx, cy - textH(ns) * 0.5f, ns, C(48, 30, 10), 1, false);
        int np = puzzlesIn(i), sv = solvedIn(i);
        std::string prog = np ? (std::to_string(sv) + "/" + std::to_string(np)) : "";
        int pts = std::max(1, ts - 1);
        float progW = prog.empty() ? 0 : (float)textW(prog, pts) + U * 3;
        float tx = cx + r + U * 3, tw = b.r.x + b.r.w - tx - progW - U * 3;
        int t1 = fitScale(CHAPTERS[i].title, tw, ts);
        int t2 = fitScale(CHAPTERS[i].sub, tw, std::max(1, ts - 2));
        float gap = U * 1.5f;
        float total = textH(t1) + gap + textH(t2);
        float ty = b.r.y + (b.r.h - total) * 0.5f + off;
        if (total > b.r.h * 0.92f) {  // мало места — только заголовок
            text(CHAPTERS[i].title, tx, b.r.y + (b.r.h - textH(t1)) * 0.5f + off, t1, COL_TEXT);
        } else {
            text(CHAPTERS[i].title, tx, ty, t1, COL_TEXT);
            text(CHAPTERS[i].sub, tx, ty + textH(t1) + gap, t2, COL_DIM, 0, false);
        }
        if (!prog.empty())
            text(prog, b.r.x + b.r.w - U * 3, cy - textH(pts) * 0.5f, pts,
                 sv == np ? C(130, 220, 120) : COL_GOLD, 2, false);
    }
}

static void drawLesson() {
    drawBackground();
    LessonLayout L = lessonLayout();
    float U = uiU();
    const LPage &p = curPage();
    const LChapter &ch = CHAPTERS[gLCh];
    int hs = std::max(1, L.ts - 1);
    std::string pg = std::to_string(gLPg + 1) + "/" + std::to_string(ch.n);
    text(pg, (float)gW - L.pad, L.hdrY, hs, COL_DIM, 2, false);
    int chs = fitScale(ch.title, gW - 2 * L.pad - textW(pg, hs) - U * 4, hs);
    text(ch.title, L.pad, L.hdrY, chs, COL_DIM, 0, false);
    int tts = fitScale(p.title, gW - 2 * L.pad, L.tsT);
    text(p.title, gW * 0.5f, L.titleY, tts, COL_GOLD, 1);

    // доска
    float fr = std::max(3.0f, L.cell * 0.09f);
    fillRRect(L.bx - fr, L.by - fr + 1, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, vgrad(C(96, 66, 42), C(58, 38, 24), L.by, L.by + L.S));
    for (int s = 0; s < 64; s++) {
        float x, y;
        lessonSqXY(L, s, x, y);
        bool light = ((s & 7) + (s >> 3)) & 1;
        fillRect(x, y, L.cell, L.cell, light ? COL_LIGHT : COL_DARK);
    }
    for (auto &m : gLMarks) {
        if (m.kind != 0) continue;
        float x, y;
        lessonSqXY(L, m.a, x, y);
        Col c = m.c == 'r' ? C(230, 60, 50, 130) : m.c == 'y' ? C(246, 222, 60, 140) : m.c == 'b' ? C(70, 130, 230, 130) : C(80, 190, 80, 130);
        fillRect(x, y, L.cell, L.cell, c);
    }
    if (gLLastFrom >= 0) {
        float x, y;
        lessonSqXY(L, gLLastFrom, x, y);
        fillRect(x, y, L.cell, L.cell, C(246, 222, 60, 95));
        lessonSqXY(L, gLLastTo, x, y);
        Col c = gLStatus == 1 ? C(90, 200, 90, 150) : gLStatus == 2 ? C(230, 70, 60, 150) : C(246, 222, 60, 125);
        fillRect(x, y, L.cell, L.cell, c);
    }
    if (gLSel >= 0) {
        float x, y;
        lessonSqXY(L, gLSel, x, y);
        fillRect(x, y, L.cell, L.cell, C(92, 178, 92, 150));
    }
    if (gLB.inCheck(gLB.side)) {
        float x, y;
        lessonSqXY(L, gLB.kingSq[gLB.side], x, y);
        radial(x + L.cell * 0.5f, y + L.cell * 0.5f, L.cell * 0.62f, C(255, 30, 20, 230), C(255, 30, 20, 0));
    }
    int cs = std::max(1, (int)(L.cell / 30.0f));
    for (int i = 0; i < 8; i++) {
        int file = gLWB ? i : 7 - i, rank = gLWB ? 7 - i : i;
        std::string fs(1, (char)('a' + file)), rs(1, (char)('1' + rank));
        bool lf = ((file + (gLWB ? 0 : 7)) & 1) != 0;
        text(fs, L.bx + i * L.cell + L.cell - textW(fs, cs) - cs * 1.5f, L.by + 8 * L.cell - textH(cs) - cs * 1.2f, cs,
             lf ? COL_DARK : COL_LIGHT, 0, false);
        bool lr = ((rank + (gLWB ? 0 : 7)) & 1) != 0;
        text(rs, L.bx + cs * 1.5f, L.by + i * L.cell + cs * 1.2f, cs, lr ? COL_DARK : COL_LIGHT, 0, false);
    }
    for (int s = 0; s < 64; s++) {
        if (!gLB.sq[s]) continue;
        float x, y;
        lessonSqXY(L, s, x, y);
        drawPiece(gLB.sq[s], x, y, L.cell);
    }
    for (auto m : gLTargets) {
        int t = eng::mTo(m);
        float x, y;
        lessonSqXY(L, t, x, y);
        float cx = x + L.cell * 0.5f, cy = y + L.cell * 0.5f;
        if (gLB.sq[t] || (eng::mFlags(m) & eng::F_EP)) ringShape(cx, cy, L.cell * 0.40f, L.cell * 0.49f, C(20, 60, 20, 95));
        else fillCircle(cx, cy, L.cell * 0.16f, C(20, 60, 20, 90));
    }
    float aw = std::max(3.0f, L.cell * 0.16f);
    for (auto &m : gLMarks) {
        if (m.kind != 1) continue;
        float x0, y0, x1, y1;
        lessonSqXY(L, m.a, x0, y0);
        lessonSqXY(L, m.b, x1, y1);
        drawArrow(x0 + L.cell * 0.5f, y0 + L.cell * 0.5f, x1 + L.cell * 0.5f, y1 + L.cell * 0.5f, aw, C(40, 160, 60, 170));
    }
    if (p.mode == LM_PUZZLE && gLShowHint && gLHint && gLStatus != 1) {
        float x0, y0, x1, y1;
        lessonSqXY(L, eng::mFrom(gLHint), x0, y0);
        lessonSqXY(L, eng::mTo(gLHint), x1, y1);
        drawArrow(x0 + L.cell * 0.5f, y0 + L.cell * 0.5f, x1 + L.cell * 0.5f, y1 + L.cell * 0.5f, aw, C(236, 160, 40, 190));
    }

    // строка состояния
    if (p.mode != LM_SHOW && p.mode != LM_GAME) {
        std::string st;
        Col sc = COL_DIM;
        if (gLStatus == 3) {
            st = "ВЕРНО! СОПЕРНИК ОТВЕЧАЕТ...";
            sc = C(130, 226, 120);
        } else if (p.mode == LM_PUZZLE && gLStatus == 0 && gLTok.size() > 3 && !gLShowHint) {
            // длинная последовательность (дебют): показываем, какой по счёту ход
            st = "ВАШ ХОД " + std::to_string(gLStep / 2 + 1) + " ИЗ " + std::to_string((gLTok.size() + 1) / 2) + " · " +
                 (gLB.side == eng::WHITE ? "БЕЛЫЕ" : "ЧЁРНЫЕ");
            sc = COL_GOLD;
        } else if (p.mode == LM_PUZZLE && gLStatus == 0 && gLStep > 0 && !gLShowHint) {
            st = "ПРОДОЛЖАЙТЕ КОМБИНАЦИЮ";
            sc = COL_GOLD;
        } else if (p.mode == LM_MOVES) {
            st = "НАЖИМАЙТЕ НА ТОЧКИ, ЧТОБЫ ПОХОДИТЬ";
        } else if (gLStatus == 1) {
            st = "ВЕРНО! ОТЛИЧНО!";
            sc = C(130, 226, 120);
        } else if (gLStatus == 2) {
            st = "НЕ ТО. ПОПРОБУЙТЕ ЕЩЁ РАЗ";
            sc = C(240, 110, 96);
        } else if (gLShowHint) {
            st = "ПОДСКАЗКА: СМОТРИТЕ НА СТРЕЛКУ";
            sc = COL_GOLD;
        } else {
            st = std::string(strcmp(p.sol, "#") == 0 ? "МАТ В 1 ХОД. " : "") + "ХОД " +
                 (gLB.side == eng::WHITE ? "БЕЛЫХ" : "ЧЁРНЫХ");
            sc = COL_GOLD;
        }
        int ss = fitScale(st, gW - 2 * L.pad, L.ts);
        text(st, gW * 0.5f, L.statusY, ss, sc, 1);
    }

    // текст урока с прокруткой
    fillRRect(L.textX, L.textY, L.textW, L.textH, U * 2.2f, C(22, 28, 40, 220));
    float ip = U * 3;
    std::string body = p.text;
    if (p.mode == LM_GAME && gLGPly > 0) {
        int i = gLGPly - 1;
        int idx = i + (gLGPos[0].side == eng::BLACK ? 1 : 0);
        std::string mv = std::to_string(idx / 2 + 1) + (idx % 2 ? "... " : ". ") + gLGSan[(size_t)i];
        std::string note;
        for (auto &nt : gLGNotes)
            if (nt.first == gLGPly) note = nt.second;
        body = "ХОД " + mv + " (" + std::to_string(gLGPly) + " ИЗ " + std::to_string(gLGMoves.size()) + ")\n" + (note.empty() ? p.text : note);
    } else if (p.mode == LM_GAME) {
        // весь вариант одной строкой: 1.e4 e5 2.Кf3 ...
        std::string line;
        int off = gLGPos[0].side == eng::BLACK ? 1 : 0;
        for (size_t i = 0; i < gLGSan.size(); i++) {
            int pl = (int)i + off;
            if (pl % 2 == 0) line += std::to_string(pl / 2 + 1) + ".";
            else if (i == 0) line += std::to_string(pl / 2 + 1) + "...";
            line += gLGSan[i] + " ";
        }
        body = std::string(p.text) + "\nХОДЫ: " + line + "\nЛИСТАЙТЕ ПО ХОДУ ИЛИ НАЖМИТЕ СМОТРЕТЬ.";
    }
    auto lines = wrapText(body, L.tsB, L.textW - 2 * ip);
    float lh = textH(L.tsB) + U * 2.4f;
    float total = lines.size() * lh + 2 * ip - U * 2.4f;
    float maxS = std::max(0.0f, total - L.textH);
    if (gLScroll > maxS) gLScroll = maxS;
    if (gLScroll < 0) gLScroll = 0;
    SDL_Rect clip;
    clip.x = (int)L.textX;
    clip.y = (int)L.textY;
    clip.w = (int)L.textW;
    clip.h = (int)std::max(1.0f, L.textH);
    SDL_RenderSetClipRect(R, &clip);
    float y = L.textY + ip - gLScroll;
    for (auto &ln : lines) {
        if (y + lh > L.textY && y < L.textY + L.textH) text(ln, L.textX + ip, y, L.tsB, COL_TEXT, 0, false);
        y += lh;
    }
    SDL_RenderSetClipRect(R, nullptr);
    if (maxS > 0) {
        float th = std::max(U * 5, L.textH * L.textH / total);
        float tp = gLScroll / maxS;
        fillRRect(L.textX + L.textW - U * 1.6f, L.textY + (L.textH - th) * tp, U * 0.8f, th, U * 0.4f, C(255, 255, 255, 70));
    }
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

// ---------- игра по сети: экраны ----------
static void drawWaitDots(float x, float y, float U) {
    Uint32 t = SDL_GetTicks();
    for (int i = 0; i < 3; i++) {
        float ph = std::sin((t / 160.0f) - i * 0.9f) * 0.5f + 0.5f;
        fillCircle(x + i * U * 3.0f, y, U * (0.6f + 0.5f * ph), withA(COL_GOLD, (int)(110 + 145 * ph)));
    }
}

static void drawTextBlock(const std::string &s, float x, float y, float w, int sc, Col c, int align) {
    auto lines = wrapText(s, sc, w);
    float lh = textH(sc) + uiU() * 2.2f;
    for (auto &ln : lines) {
        text(ln, align == 1 ? x + w * 0.5f : x, y, sc, c, align, false);
        y += lh;
    }
}

static void drawNet() {
    drawBackground();
    float W = (float)gW, H = (float)gH, U = uiU();
    int ts = uiTS();
    float top = H * 0.05f;
    int tts = fitScale("ИГРА ПО СЕТИ", W * 0.9f, ts * 2);
    text("ИГРА ПО СЕТИ", W * 0.5f, top + U * 6, tts, COL_GOLD, 1);
    float bw = std::min(W * 0.9f, U * 90.0f), x = (W - bw) * 0.5f;
    float sy = top + U * 6 + textH(tts) + U * 3;
    int sm = std::max(1, ts - 1);
    float y = top + U * 30;
    if (gNetUI == NU_MENU) {
        drawTextBlock("ОБА ТЕЛЕФОНА ДОЛЖНЫ БЫТЬ В ОДНОЙ СЕТИ ВАЙ-ФАЙ ИЛИ ОДИН РАЗДАЁТ ТОЧКУ ДОСТУПА ДРУГОМУ", x, sy, bw, sm, COL_DIM, 1);
        text("ВАШ ЦВЕТ", x, y, ts, COL_TEXT);
        float bh = std::max(36.0f, U * 12.5f);
        y += textH(ts) + U * 3 + bh * 1.35f + U * 7;
        text("ЧАСЫ (НА КАЖДОГО)", x, y, ts, COL_TEXT);
    } else if (gNetUI == NU_WAIT) {
        text("ОЖИДАНИЕ СОПЕРНИКА", W * 0.5f, y, ts + 1, COL_TEXT, 1);
        drawWaitDots(W * 0.5f - U * 3, y + textH(ts + 1) + U * 5, U);
        y += textH(ts + 1) + U * 12;
        text("ВАШ АДРЕС В СЕТИ:", W * 0.5f, y, sm, COL_DIM, 1, false);
        y += textH(sm) + U * 3;
        std::string ip = gNet.myIp.empty() ? "НЕ ОПРЕДЕЛЁН" : gNet.myIp;
        int is = fitScale(ip, bw, ts * 2);
        text(ip, W * 0.5f, y, is, COL_GOLD, 1);
        y += textH(is) + U * 8;
        drawTextBlock("НА ВТОРОМ ТЕЛЕФОНЕ ОТКРОЙТЕ: ПО СЕТИ - ПОДКЛЮЧИТЬСЯ. ИГРА НАЙДЁТСЯ САМА, ИЛИ ВВЕДИТЕ ЭТОТ АДРЕС ВРУЧНУЮ.",
                      x, y, bw, sm, COL_TEXT, 1);
    } else if (gNetUI == NU_JOIN) {
        text("ПОИСК ИГР В СЕТИ", W * 0.5f, top + U * 24, ts + 1, COL_TEXT, 1);
        drawWaitDots(W * 0.5f + textW("ПОИСК ИГР В СЕТИ", ts + 1) * 0.5f + U * 3, top + U * 24 + textH(ts + 1) * 0.5f, U);
        if (gFound.empty())
            drawTextBlock("ПОКА НИЧЕГО НЕ НАЙДЕНО. СОЗДАЙТЕ ИГРУ НА ВТОРОМ ТЕЛЕФОНЕ. ЕСЛИ ОНА НЕ ПОЯВЛЯЕТСЯ, ВВЕДИТЕ АДРЕС ВРУЧНУЮ.",
                          x, top + U * 36, bw, sm, COL_DIM, 1);
    } else if (gNetUI == NU_KEYPAD) {
        text("АДРЕС ИГРЫ", W * 0.5f, top + U * 22, ts, COL_TEXT, 1);
        float fy = top + U * 30, fh = U * 14;
        fillRRect(x, fy, bw, fh, U * 2.5f, C(22, 28, 40, 240));
        fillRRect(x, fy + fh - U * 0.6f, bw, U * 0.6f, 0, COL_GOLD);
        if (gNetIpInput.empty()) {
            int ps = fitScale("НАПРИМЕР 192.168.1.5", bw * 0.9f, ts);
            text("НАПРИМЕР 192.168.1.5", W * 0.5f, fy + (fh - textH(ps)) * 0.5f, ps, C(110, 118, 132), 1, false);
        } else {
            int is = fitScale(gNetIpInput, bw * 0.9f, ts + 2);
            text(gNetIpInput, W * 0.5f, fy + (fh - textH(is)) * 0.5f, is, COL_GOLD, 1);
        }
    } else if (gNetUI == NU_CONNECTING) {
        text("ПОДКЛЮЧЕНИЕ", W * 0.5f, y, ts + 1, COL_TEXT, 1);
        drawWaitDots(W * 0.5f - U * 3, y + textH(ts + 1) + U * 5, U);
        int is = fitScale(gNet.peerIp, bw, ts + 2);
        text(gNet.peerIp, W * 0.5f, y + textH(ts + 1) + U * 12, is, COL_GOLD, 1);
    }
    if (!gNetMsg.empty() && gNetUI != NU_WAIT && gNetUI != NU_CONNECTING) {
        float bh2 = std::max(40.0f, U * 14.0f);
        float my = H - U * 6 - bh2 - (gNetUI == NU_MENU ? 2 : 1) * (bh2 + U * 3) - textH(ts) - U * 4;
        int ms = fitScale(gNetMsg, bw, ts);
        text(gNetMsg, W * 0.5f, my, ms, C(240, 110, 96), 1);
    }
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

static void drawToast() {
    if (gToast.empty() || SDL_GetTicks() > gToastUntil) return;
    float U = uiU();
    int ts = uiTS();
    int sc = fitScale(gToast, gW * 0.85f, ts);
    float w = textW(gToast, sc) + U * 8, h = textH(sc) + U * 6;
    float x = (gW - w) * 0.5f, y = gH * 0.80f - h;
    if (gScreen == SC_EDITOR) y = edLayout().palY1 - h - U * 3;  // не закрывать строку проверки
    fillRRect(x, y + U * 0.6f, w, h, h * 0.5f, C(0, 0, 0, 110));
    fillRRect(x, y, w, h, h * 0.5f, C(236, 230, 214, 245));
    text(gToast, gW * 0.5f, y + (h - textH(sc)) * 0.5f, sc, C(30, 30, 34), 1, false);
}

// ---------- экран разбора партии ----------
static const char *CLS_SYM[4] = {"", "?!", "?", "??"};
static const char *CLS_NAME[4] = {"", "НЕТОЧНОСТЬ", "ОШИБКА", "ГРУБАЯ ОШИБКА"};
static Col clsCol(int c) {
    switch (c) {
        case 1: return C(240, 210, 90);
        case 2: return C(245, 150, 70);
        case 3: return C(240, 90, 80);
        default: return COL_TEXT;
    }
}
static std::string moveLabel(int i) {
    std::string san = gRv.g.san[(size_t)i];
    int p = i + gRv.g.off();
    return std::to_string(p / 2 + 1) + (p % 2 ? "... " : ". ") + san;
}
static std::string fmtEval(int whiteScore) {
    if (std::abs(whiteScore) > eng::MATE - 300) {
        int plies = eng::MATE - std::abs(whiteScore);
        return std::string(whiteScore > 0 ? "+" : "-") + "М" + std::to_string((plies + 1) / 2);
    }
    char b[32];
    snprintf(b, sizeof b, "%+.1f", whiteScore / 100.0);
    return b;
}

static void rvSqXY(const RvLayout &L, int s, float &x, float &y) {
    int f = s & 7, r = s >> 3;
    int col = gRv.wb ? f : 7 - f, row = gRv.wb ? 7 - r : r;
    x = L.bx + col * L.cell;
    y = L.by + row * L.cell;
}

static void drawReview() {
    drawBackground();
    RvLayout L = rvLayout();
    float W = (float)gW, U = uiU();
    int n = (int)gRv.g.moves.size();
    text("РАЗБОР ПАРТИИ", W * 0.5f, L.titleY, L.ts + 1, COL_GOLD, 1);
    // общая оценка игры
    if (gRv.ready) {
        auto word = [](int r) -> const char * {
            if (r >= 10) return "ИДЕАЛЬНО";
            if (r >= 8) return "ОТЛИЧНО";
            if (r >= 6) return "ХОРОШО";
            if (r >= 4) return "СРЕДНЕ";
            return "СЛАБО";
        };
        auto rcol = [](int r) -> Col {
            if (r >= 8) return C(130, 226, 120);
            if (r >= 6) return COL_GOLD;
            if (r >= 4) return C(245, 170, 80);
            return C(240, 100, 90);
        };
        std::string line;
        Col lc;
        if (gRv.focus >= 0) {
            int r = gRv.rate[gRv.focus];
            line = "ВАША ИГРА: " + std::to_string(r) + " ИЗ 10 · " + word(r);
            lc = rcol(r);
        } else {
            line = "БЕЛЫЕ " + std::to_string(gRv.rate[0]) + " ИЗ 10 · ЧЁРНЫЕ " + std::to_string(gRv.rate[1]) + " ИЗ 10";
            lc = COL_GOLD;
        }
        int rs = fitScale(line, W - 2 * L.pad, L.ts + 2);
        float bw = textW(line, rs) + U * 8, bh = textH(rs) + U * 3;
        float bx = (W - bw) * 0.5f, by = L.rateY - U * 1.5f;
        fillRRect(bx, by, bw, bh, bh * 0.5f, C(255, 255, 255, 18));
        text(line, W * 0.5f, L.rateY, rs, lc, 1);
    }
    // итоги по сторонам
    if (gRv.ready) {
        float y = L.sumY;
        for (int s = 0; s < 2; s++) {
            std::string who = gRv.mode == MODE_TWO ? sideName(s, true) : (s == gRv.human ? "ВЫ" : (gRv.mode == MODE_BOT ? "БОТ" : "СОПЕРНИК"));
            std::string a = who + ": " + std::to_string(gRv.rate[s]) + "/10 · ТОЧНОСТЬ " + std::to_string(gRv.acc[s]) + "%";
            float x = L.pad;
            text(a, x, y, L.tsS, s == gRv.focus || gRv.focus < 0 ? COL_TEXT : COL_DIM, 0, false);
            x = W - L.pad;
            for (int c = 3; c >= 1; c--) {
                std::string t = std::string(CLS_SYM[c]) + " " + std::to_string(gRv.cnt[s][c]);
                text(t, x, y, L.tsS, clsCol(c), 2, false);
                x -= textW(t, L.tsS) + U * 4;
            }
            y += textH(L.tsS) + U * 2;
        }
    }
    // доска: позиция перед обсуждаемым ходом
    int idx = gRv.k - 1;
    const eng::Board &b = gRv.pos[(size_t)std::max(0, idx)];
    float fr = std::max(3.0f, L.cell * 0.09f);
    fillRRect(L.bx - fr, L.by - fr + 1, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, vgrad(C(96, 66, 42), C(58, 38, 24), L.by, L.by + L.S));
    for (int s = 0; s < 64; s++) {
        float x, y;
        rvSqXY(L, s, x, y);
        bool light = ((s & 7) + (s >> 3)) & 1;
        fillRect(x, y, L.cell, L.cell, light ? COL_LIGHT : COL_DARK);
    }
    if (idx >= 1) {  // предыдущий ход соперника
        eng::Move pm = gRv.g.moves[(size_t)idx - 1];
        float x, y;
        rvSqXY(L, eng::mFrom(pm), x, y);
        fillRect(x, y, L.cell, L.cell, C(246, 222, 60, 80));
        rvSqXY(L, eng::mTo(pm), x, y);
        fillRect(x, y, L.cell, L.cell, C(246, 222, 60, 110));
    }
    if (b.inCheck(b.side)) {
        float x, y;
        rvSqXY(L, b.kingSq[b.side], x, y);
        radial(x + L.cell * 0.5f, y + L.cell * 0.5f, L.cell * 0.62f, C(255, 30, 20, 230), C(255, 30, 20, 0));
    }
    for (int s = 0; s < 64; s++) {
        if (!b.sq[s]) continue;
        float x, y;
        rvSqXY(L, s, x, y);
        drawPiece(b.sq[s], x, y, L.cell);
    }
    float aw = std::max(3.0f, L.cell * 0.15f);
    if (gRv.ready && idx >= 0 && idx < n) {
        eng::Move pm = gRv.g.moves[(size_t)idx], bm = gRv.best[(size_t)idx];
        float x0, y0, x1, y1;
        if (bm && bm != pm && !gRv.book[(size_t)idx]) {
            rvSqXY(L, eng::mFrom(bm), x0, y0);
            rvSqXY(L, eng::mTo(bm), x1, y1);
            drawArrow(x0 + L.cell * 0.5f, y0 + L.cell * 0.5f, x1 + L.cell * 0.5f, y1 + L.cell * 0.5f, aw, C(40, 170, 70, 190));
        }
        rvSqXY(L, eng::mFrom(pm), x0, y0);
        rvSqXY(L, eng::mTo(pm), x1, y1);
        int c = gRv.cls[(size_t)idx];
        Col ac = c == 0 ? C(70, 130, 230, 170) : withA(clsCol(c), 200);
        drawArrow(x0 + L.cell * 0.5f, y0 + L.cell * 0.5f, x1 + L.cell * 0.5f, y1 + L.cell * 0.5f, aw, ac);
    }
    // шкала оценки
    if (gRv.ready) {
        float f = (winChance(rvWhiteScore(std::max(0, idx))) + 1) * 0.5f;
        fillRRect(L.bx, L.evalY, L.S, L.evalH, L.evalH * 0.5f, C(30, 30, 34));
        fillRRect(L.bx, L.evalY, std::max(L.evalH, L.S * f), L.evalH, L.evalH * 0.5f, C(236, 232, 222));
        fillRect(L.bx + L.S * 0.5f - 1, L.evalY - U * 0.6f, 2, L.evalH + U * 1.2f, C(236, 186, 92));
    }
    // описание хода
    float y = L.infoY;
    float lh = textH(L.ts) + U * 2;
    if (!gRv.ready) {
        int prog = gRvJob ? gRvJob->progress.load() : 0;
        int total = n;
        text("АНАЛИЗ ПАРТИИ...", W * 0.5f, y, L.ts, COL_TEXT, 1);
        float bw = L.S, bx = (W - bw) * 0.5f, by = y + lh + U * 2;
        fillRRect(bx, by, bw, U * 3, U * 1.5f, C(30, 38, 52));
        fillRRect(bx, by, std::max(U * 3, bw * prog / std::max(1, total)), U * 3, U * 1.5f, COL_GOLD);
        text(std::to_string(prog * 100 / std::max(1, total)) + "%", W * 0.5f, by + U * 5, L.tsS, COL_DIM, 1, false);
    } else if (idx < 0) {
        text("НАЧАЛО ПАРТИИ", L.pad, y, L.ts, COL_TEXT);
        text("ЛИСТАЙТЕ ХОДЫ ИЛИ ВЫБЕРИТЕ ОШИБКУ НИЖЕ", L.pad, y + lh, fitScale("ЛИСТАЙТЕ ХОДЫ ИЛИ ВЫБЕРИТЕ ОШИБКУ НИЖЕ", W - 2 * L.pad, L.tsS), COL_DIM, 0, false);
    } else {
        int c = gRv.cls[(size_t)idx];
        std::string l1 = moveLabel(idx) + CLS_SYM[c];
        text(l1, L.pad, y, L.ts, clsCol(c));
        bool bk = gRv.book[(size_t)idx], fo = gRv.forced[(size_t)idx];
        std::string tag = c ? CLS_NAME[c]
                            : bk ? "ДЕБЮТНАЯ ТЕОРИЯ"
                                 : fo ? "ЕДИНСТВЕННЫЙ ХОД" : (gRv.isBest[(size_t)idx] ? "ЛУЧШИЙ ХОД" : "ХОРОШИЙ ХОД");
        Col tc = c ? clsCol(c) : (bk ? C(140, 196, 255) : C(130, 220, 120));
        int tgs = fitScale(tag, W - 2 * L.pad - textW(l1, L.ts) - U * 4, L.tsS);
        text(tag, W - L.pad, y + textH(L.ts) - textH(tgs), tgs, tc, 2, false);
        y += lh;
        if (bk) {
            text("ХОД ИЗ ДЕБЮТНОГО СПРАВОЧНИКА", L.pad, y, L.tsS, C(140, 196, 255), 0, false);
        } else if (!gRv.isBest[(size_t)idx] && gRv.best[(size_t)idx]) {
            std::string bs = "ЛУЧШЕ: " + eng::toSAN(gRv.pos[(size_t)idx], gRv.best[(size_t)idx]);
            text(bs, L.pad, y, L.tsS, C(130, 220, 120), 0, false);
        } else {
            text("ЭТО ХОД ДВИЖКА", L.pad, y, L.tsS, C(130, 220, 120), 0, false);
        }
        y += textH(L.tsS) + U * 2;
        const eng::MoveVerdict &mv = gRv.res[(size_t)idx];
        std::string ev = "ОЦЕНКА: " + fmtEval(rvWhite(idx, mv.best)) + " -> " + fmtEval(rvWhite(idx, mv.played));
        text(ev, L.pad, y, L.tsS, COL_DIM, 0, false);
        text("ГЛУБИНА " + std::to_string(mv.depth), W - L.pad, y, L.tsS, C(110, 118, 132), 2, false);
    }
    // список ошибок
    if (gRv.ready && L.listH > U * 6) {
        fillRRect(L.pad, L.listY, W - 2 * L.pad, L.listH, U * 2.2f, C(22, 28, 40, 220));
        std::string hdr = gRv.focus < 0 ? "ОШИБКИ В ПАРТИИ" : "ВАШИ ОШИБКИ";
        text(hdr, L.pad + U * 3, L.listY + U * 2, L.tsS, COL_GOLD, 0, false);
        float ly0 = L.listY + U * 3 + textH(L.tsS) + U * 2;
        float rh = L.rowH;
        float areaH = L.listY + L.listH - ly0 - U * 1.5f;
        float total = gRv.list.size() * rh;
        float maxS = std::max(0.0f, total - areaH);
        if (gRv.scroll > maxS) gRv.scroll = maxS;
        if (gRv.scroll < 0) gRv.scroll = 0;
        if (gRv.list.empty()) {
            drawTextBlock("ОШИБОК НЕ НАЙДЕНО. ОТЛИЧНАЯ ИГРА!", L.pad + U * 3, ly0, W - 2 * L.pad - U * 6, L.tsS, C(130, 220, 120), 0);
        } else {
            SDL_Rect clip;
            clip.x = (int)L.pad;
            clip.y = (int)ly0;
            clip.w = (int)(W - 2 * L.pad);
            clip.h = (int)std::max(1.0f, areaH);
            SDL_RenderSetClipRect(R, &clip);
            float ry = ly0 - gRv.scroll;
            for (int i : gRv.list) {
                if (ry + rh > ly0 && ry < ly0 + areaH) {
                    int c = gRv.cls[(size_t)i];
                    if (i == idx) fillRRect(L.pad + U * 1.5f, ry - U * 0.8f, W - 2 * L.pad - U * 3, rh - U * 0.4f, U, C(255, 255, 255, 22));
                    std::string a = moveLabel(i) + CLS_SYM[c];
                    text(a, L.pad + U * 3, ry, L.tsS, clsCol(c), 0, false);
                    if (gRv.best[(size_t)i]) {
                        std::string bb = "ЛУЧШЕ " + eng::toSAN(gRv.pos[(size_t)i], gRv.best[(size_t)i]);
                        text(bb, W - L.pad - U * 3, ry, L.tsS, C(130, 200, 120), 2, false);
                    }
                }
                ry += rh;
            }
            SDL_RenderSetClipRect(R, nullptr);
        }
    }
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
}

// какая строка списка ошибок под пальцем
static int rvListHit(float x, float y) {
    RvLayout L = rvLayout();
    float U = uiU();
    float ly0 = L.listY + U * 3 + textH(L.tsS) + U * 2;
    if (x < L.pad || x > gW - L.pad || y < ly0 || y > L.listY + L.listH) return -1;
    int r = (int)std::floor((y - ly0 + gRv.scroll + U * 0.8f) / L.rowH);
    if (r < 0 || r >= (int)gRv.list.size()) return -1;
    return gRv.list[(size_t)r];
}

// ---------- экран расстановки фигур ----------
static void edSqXY(const EdLayout &L, int s, float &x, float &y) {
    x = L.bx + (s & 7) * L.cell;
    y = L.by + (7 - (s >> 3)) * L.cell;
}
static int edXYToSq(const EdLayout &L, float x, float y) {
    if (x < L.bx || y < L.by || x >= L.bx + L.S || y >= L.by + L.S) return -1;
    int col = (int)((x - L.bx) / L.cell), row = (int)((y - L.by) / L.cell);
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return (7 - row) * 8 + col;
}

static void drawEditor() {
    drawBackground();
    EdLayout L = edLayout();
    float W = (float)gW, U = uiU();
    int tsT = fitScale("РАССТАНОВКА ФИГУР", W - 2 * L.pad, L.ts + 1);
    text("РАССТАНОВКА ФИГУР", W * 0.5f, L.titleY, tsT, COL_GOLD, 1);
    // доска
    float fr = std::max(3.0f, L.cell * 0.09f);
    fillRRect(L.bx - fr, L.by - fr + 1, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, vgrad(C(96, 66, 42), C(58, 38, 24), L.by, L.by + L.S));
    for (int s = 0; s < 64; s++) {
        float x, y;
        edSqXY(L, s, x, y);
        bool light = ((s & 7) + (s >> 3)) & 1;
        fillRect(x, y, L.cell, L.cell, light ? COL_LIGHT : COL_DARK);
    }
    int cs = std::max(1, (int)(L.cell / 30.0f));
    for (int i = 0; i < 8; i++) {
        std::string fs(1, (char)('a' + i)), rs(1, (char)('8' - i));
        text(fs, L.bx + i * L.cell + L.cell - textW(fs, cs) - cs * 1.5f, L.by + 8 * L.cell - textH(cs) - cs * 1.2f, cs,
             (i & 1) ? COL_DARK : COL_LIGHT, 0, false);
        text(rs, L.bx + cs * 1.5f, L.by + i * L.cell + cs * 1.2f, cs, (i & 1) ? COL_DARK : COL_LIGHT, 0, false);
    }
    bool dragBoard = gEdDown && gEdMoved && gEdFrom >= 0 && gEdSq[gEdFrom];
    bool dragPal = gPtr.down && gPressed >= B_ED_PAL0 && gPressed < B_ED_PAL0 + 12;
    if (dragPal) {
        dragPal = false;
        for (auto &b : gScreenBtns)
            if (b.id == gPressed && !inRect(b.r, gPtr.x, gPtr.y)) dragPal = true;
    }
    // король под шахом — подсветка
    {
        eng::Board b;
        bool kings = false;
        int wk = 0, bk = 0;
        for (int i = 0; i < 64; i++) {
            if (gEdSq[i] == eng::mkPiece(eng::WHITE, eng::KING)) wk++;
            if (gEdSq[i] == eng::mkPiece(eng::BLACK, eng::KING)) bk++;
        }
        kings = wk == 1 && bk == 1;
        if (kings && b.setFEN(edFen()))
            for (int c = 0; c < 2; c++)
                if (b.inCheck(c)) {
                    float x, y;
                    edSqXY(L, b.kingSq[c], x, y);
                    radial(x + L.cell * 0.5f, y + L.cell * 0.5f, L.cell * 0.62f, C(255, 30, 20, 230), C(255, 30, 20, 0));
                }
    }
    for (int s = 0; s < 64; s++) {
        if (!gEdSq[s] || (dragBoard && s == gEdFrom)) continue;
        float x, y;
        edSqXY(L, s, x, y);
        drawPiece(gEdSq[s], x, y, L.cell);
    }
    if (dragBoard || dragPal) {
        int hs = edXYToSq(L, gPtr.x, gPtr.y);
        if (hs >= 0) {
            float x, y;
            edSqXY(L, hs, x, y);
            float w = std::max(2.0f, L.cell * 0.06f);
            Col hc = C(255, 255, 255, 170);
            fillRect(x, y, L.cell, w, hc);
            fillRect(x, y + L.cell - w, L.cell, w, hc);
            fillRect(x, y, w, L.cell, hc);
            fillRect(x + L.cell - w, y, w, L.cell, hc);
        }
    }
    // счёт фигур и проверка
    int wt, wp, bt, bp;
    edCount(eng::WHITE, wt, wp);
    edCount(eng::BLACK, bt, bp);
    std::string cnt = "БЕЛЫХ " + std::to_string(wt) + " (ПЕШЕК " + std::to_string(wp) + ") · ЧЁРНЫХ " + std::to_string(bt) +
                      " (ПЕШЕК " + std::to_string(bp) + ")";
    text(cnt, W * 0.5f, L.infoY, fitScale(cnt, W - 2 * L.pad, L.tsS), COL_DIM, 1, false);
    std::string msg;
    bool ok = edCheck(msg);
    text(msg, W * 0.5f, L.infoY + textH(L.tsS) + U * 2.5f, fitScale(msg, W - 2 * L.pad, L.tsS), ok ? C(130, 226, 120) : C(240, 110, 96), 1, false);
    drawButtons(gScreenBtns, gOverlay == OV_NONE);
    // фигура в пальце
    float ds = L.cell * 1.3f;
    if (dragBoard) drawPiece(gEdSq[gEdFrom], gPtr.x - ds * 0.5f, gPtr.y - ds * 0.85f, ds);
    if (dragPal) {
        int i = gPressed - B_ED_PAL0;
        drawPiece(eng::mkPiece(i / 6, ED_TYPES[i % 6]), gPtr.x - ds * 0.5f, gPtr.y - ds * 0.85f, ds);
    }
}

// ---------- окна поверх ----------
static void drawPanel(const Panel &p) {
    float U = uiU();
    fillRRect(p.x, p.y + U, p.w, p.h, U * 3.5f, C(0, 0, 0, 120));
    fillRRect(p.x, p.y, p.w, p.h, U * 3.5f, C(96, 112, 138));
    float b = std::max(1.0f, U * 0.4f);
    fillRRect(p.x + b, p.y + b, p.w - 2 * b, p.h - 2 * b, U * 3.5f - b, vgrad(C(48, 60, 80), C(30, 38, 52), p.y, p.y + p.h));
}

static std::string reasonText() {
    const Game &g = gM.g;
    switch (g.reason) {
        case R_MATE: return "МАТ";
        case R_STALEMATE: return "ПАТ";
        case R_RESIGN: return (g.loser >= 0 ? sideName(g.loser, true) : std::string("ИГРОК")) + " СДАЛИСЬ";
        case R_TIME:
            if (g.result == RES_DRAW) return "ВРЕМЯ ВЫШЛО, НО МАТ НЕВОЗМОЖЕН";
            return "У " + sideName(g.loser, false) + " ВЫШЛО ВРЕМЯ";
        case R_FIFTY: return "ПРАВИЛО 50 ХОДОВ";
        case R_REPEAT: return "ТРОЕКРАТНОЕ ПОВТОРЕНИЕ";
        case R_MATERIAL: return "НЕДОСТАТОЧНО МАТЕРИАЛА";
        case R_AGREE: return "ПО СОГЛАСИЮ";
        case R_LEFT: return "СОПЕРНИК ПОКИНУЛ ИГРУ";
        default: return "";
    }
}

static void drawOverlay() {
    if (gOverlay == OV_NONE) return;
    fillRect(0, 0, (float)gW, (float)gH, C(0, 0, 0, 140));
    float U = uiU();
    int ts = uiTS();
    if (gOverlay == OV_CONFIRM) {
        Panel p = overlayPanel(52);
        drawPanel(p);
        std::string q1, q2;
        if (gConfirm == CF_RESIGN) { q1 = "СДАТЬСЯ?"; q2 = "ПАРТИЯ БУДЕТ ПРОИГРАНА"; }
        else if (gConfirm == CF_NEW && gM.mode == MODE_NET) { q1 = "НОВАЯ ПАРТИЯ?"; q2 = "ПРЕДЛОЖИТЬ СОПЕРНИКУ НАЧАТЬ ЗАНОВО"; }
        else if (gConfirm == CF_NEW) { q1 = "НОВАЯ ПАРТИЯ?"; q2 = "ТЕКУЩАЯ ПАРТИЯ НЕ ЗАВЕРШЕНА"; }
        else if (gConfirm == CF_NET_DRAW) { q1 = "НИЧЬЯ?"; q2 = "СОПЕРНИК ПРЕДЛАГАЕТ НИЧЬЮ"; }
        else if (gConfirm == CF_NET_NEW) { q1 = "НОВАЯ ПАРТИЯ?"; q2 = "СОПЕРНИК ПРЕДЛАГАЕТ СЫГРАТЬ ЕЩЁ"; }
        else if (gConfirm == CF_NET_LEAVE) { q1 = "ПОКИНУТЬ ИГРУ?"; q2 = "ВАМ БУДЕТ ЗАСЧИТАНО ПОРАЖЕНИЕ"; }
        else if (gConfirm == CF_NET_LOST) { q1 = "СВЯЗЬ ПОТЕРЯНА"; q2 = "СОПЕРНИК НЕ ОТВЕЧАЕТ, ПАРТИЯ ПРЕРВАНА"; }
        else { q1 = "СБРОСИТЬ?"; q2 = "ВСЯ СТАТИСТИКА БУДЕТ УДАЛЕНА"; }
        int s1 = fitScale(q1, p.w * 0.9f, ts + 2), s2 = fitScale(q2, p.w * 0.9f, ts);
        text(q1, p.x + p.w * 0.5f, p.y + U * 8, s1, COL_GOLD, 1);
        text(q2, p.x + p.w * 0.5f, p.y + U * 8 + textH(s1) + U * 5, s2, COL_DIM, 1, false);
    } else if (gOverlay == OV_CHOOSE) {
        Panel p = overlayPanel(78);
        drawPanel(p);
        text("КАК ИГРАТЬ?", p.x + p.w * 0.5f, p.y + U * 7, fitScale("КАК ИГРАТЬ?", p.w * 0.9f, ts + 2), COL_GOLD, 1);
        std::string sub = "В ВАШЕЙ РАССТАНОВКЕ";
        text(sub, p.x + p.w * 0.5f, p.y + U * 7 + textH(ts + 2) + U * 3, fitScale(sub, p.w * 0.9f, ts), COL_DIM, 1, false);
    } else if (gOverlay == OV_RESULT) {
        Panel p = overlayPanel(120);
        drawPanel(p);
        const Game &g = gM.g;
        std::string t1;
        Col tc = COL_GOLD;
        int winner = g.result == RES_WHITE ? eng::WHITE : (g.result == RES_BLACK ? eng::BLACK : -1);
        if (g.result == RES_DRAW) t1 = "НИЧЬЯ";
        else if (gM.mode != MODE_TWO) {
            if (winner == gM.human) { t1 = "ПОБЕДА!"; tc = C(140, 226, 130); }
            else { t1 = "ПОРАЖЕНИЕ"; tc = C(236, 120, 106); }
        } else {
            t1 = "ПОБЕДИЛИ " + sideName(winner, true);
        }
        float ps = U * 16;
        float cy = p.y + U * 5;
        if (winner >= 0) {
            drawPiece(eng::mkPiece(winner, eng::KING), p.x + p.w * 0.5f - ps * 0.5f, cy, ps);
        } else {
            drawPiece(eng::mkPiece(eng::WHITE, eng::KING), p.x + p.w * 0.5f - ps * 0.9f, cy, ps);
            drawPiece(eng::mkPiece(eng::BLACK, eng::KING), p.x + p.w * 0.5f - ps * 0.1f, cy, ps);
        }
        cy += ps + U * 2;
        int s1 = fitScale(t1, p.w * 0.9f, ts * 2);
        text(t1, p.x + p.w * 0.5f, cy, s1, tc, 1);
        cy += textH(s1) + U * 4;
        std::string r = reasonText();
        int s2 = fitScale(r, p.w * 0.9f, ts);
        text(r, p.x + p.w * 0.5f, cy, s2, COL_TEXT, 1, false);
        cy += textH(s2) + U * 3;
        std::string mv = "ХОДОВ: " + std::to_string((g.moves.size() + g.off() + 1) / 2);
        text(mv, p.x + p.w * 0.5f, cy, std::max(1, ts - 1), COL_DIM, 1, false);
    } else if (gOverlay == OV_PROMO) {
        Panel p = overlayPanel(50);
        drawPanel(p);
        int s1 = fitScale("ПРЕВРАЩЕНИЕ ПЕШКИ", p.w * 0.9f, ts + 1);
        text("ПРЕВРАЩЕНИЕ ПЕШКИ", p.x + p.w * 0.5f, p.y + U * 7, s1, COL_GOLD, 1);
        text("ВЫБЕРИТЕ ФИГУРУ", p.x + p.w * 0.5f, p.y + U * 7 + textH(s1) + U * 3, std::max(1, ts - 1), COL_DIM, 1, false);
    }
    drawButtons(gOverBtns, true);
}

static void render() {
    SDL_SetRenderDrawBlendMode(R, SDL_BLENDMODE_BLEND);
    SDL_SetRenderDrawColor(R, 12, 15, 22, 255);
    SDL_RenderClear(R);
    ensurePieceTex((int)gameLayout().cell);  // один размер текстур фигур для всех экранов
    switch (gScreen) {
        case SC_MENU: drawMenu(); break;
        case SC_SETUP: drawSetup(); break;
        case SC_STATS: drawStats(); break;
        case SC_LEARN: drawLearn(); break;
        case SC_LESSON: drawLesson(); break;
        case SC_NET: drawNet(); break;
        case SC_REVIEW: drawReview(); break;
        case SC_EDITOR: drawEditor(); break;
        case SC_GAME: drawGame(); break;
    }
    drawOverlay();
    drawToast();
}

// =====================================================================
//                              ВВОД
// =====================================================================
static void goMenu() {
    cancelReview();
    if (gM.mode == MODE_NET) netLeave(true);
    gViewPly = -1;
    cancelBot();
    clearSel();
    gOverlay = OV_NONE;
    gResultPending = false;
    gScreen = SC_MENU;
    saveAll();
}

static void netCancel() {
    gNetMsg.clear();
    switch (gNetUI) {
        case NU_WAIT: netCloseAll(); gNetUI = NU_MENU; break;
        case NU_CONNECTING: netCloseAll(); netScanStart(); gNetUI = NU_JOIN; break;
        case NU_JOIN: netCloseAll(); gNetUI = NU_MENU; break;
        case NU_KEYPAD: netScanStart(); gNetUI = NU_JOIN; break;
        default: netCloseAll(); gScreen = SC_MENU; break;
    }
}

// Закрыть окно подтверждения «нет»; на предложение соперника — отказ
static void confirmCancel() {
    if (gConfirm == CF_NET_DRAW || gConfirm == CF_NET_NEW) netSendLine("DECLINE");
    gOverlay = OV_NONE;
    gConfirm = CF_NONE;
}

static void netJoinIp(const std::string &ip) {
    if (!validIp(ip)) {
        gNetMsg = "НЕВЕРНЫЙ АДРЕС";
        return;
    }
    if (netConnect(ip)) {
        gNetMsg.clear();
        gNetUI = NU_CONNECTING;
    } else {
        gNetMsg = "НЕ УДАЛОСЬ ПОДКЛЮЧИТЬСЯ";
    }
}

static void leaveGameAsk() {
    if (gM.mode == MODE_NET && gM.g.result == RES_NONE && netConnected() && !gM.g.moves.empty()) {
        gConfirm = CF_NET_LEAVE;
        gOverlay = OV_CONFIRM;
        clearSel();
    } else {
        goMenu();
    }
}

static void onButton(int id) {
    playSound(SND_CLICK);
    switch (id) {
        case B_CONTINUE:
            gScreen = SC_GAME;
            gViewSide = gM.g.cur.side;
            gLastTick = SDL_GetTicks();
            clearSel();
            startBot();
            break;
        case B_PLAY_BOT: gCustomFen.clear(); gSetupMode = MODE_BOT; gScreen = SC_SETUP; break;
        case B_PLAY_TWO: gCustomFen.clear(); gSetupMode = MODE_TWO; gScreen = SC_SETUP; break;
        case B_EDITOR: edEnsure(); gScreen = SC_EDITOR; break;
        case B_ED_ERASER: gEdTool = 0; break;
        case B_ED_WHITE: gEdSide = eng::WHITE; break;
        case B_ED_BLACK: gEdSide = eng::BLACK; break;
        case B_ED_CLEAR: edClear(); break;
        case B_ED_START: {
            eng::Board b;
            b.setStart();
            edLoadBoard(b);
            break;
        }
        case B_ED_GAME:
            if (gM.active) edLoadBoard(gM.g.cur);
            break;
        case B_ED_PLAY: {
            std::string m;
            if (edCheck(m)) gOverlay = OV_CHOOSE;
            else toast(m);
            break;
        }
        case B_ED_BOT:
        case B_ED_TWO:
            gOverlay = OV_NONE;
            gCustomFen = edFen();
            gSetupMode = id == B_ED_BOT ? MODE_BOT : MODE_TWO;
            gScreen = SC_SETUP;
            break;
        case B_STATS: gScreen = SC_STATS; break;
        case B_SOUND: gSoundOn = !gSoundOn; saveAll(); break;
        case B_EXIT: gRunning = false; break;
        case B_LVL1: case B_LVL2: case B_LVL3: case B_LVL4: case B_LVL5: gSet.level = id - B_LVL1 + 1; saveAll(); break;
        case B_COL_W: case B_COL_B: case B_COL_R: gSet.color = id - B_COL_W; saveAll(); break;
        case B_CLK0: case B_CLK1: case B_CLK2: case B_CLK3: gSet.clock = id - B_CLK0; saveAll(); break;
        case B_START: newMatch(gSetupMode, gSet.level, gSetupMode == MODE_BOT ? gSet.color : 0, gSet.clock, gCustomFen); break;
        case B_BACK:
            if (gScreen == SC_NET) netCloseAll();
            gScreen = (gScreen == SC_SETUP && !gCustomFen.empty()) ? SC_EDITOR : SC_MENU;
            break;
        case B_UNDO: doUndo(); break;
        case B_RESIGN: gConfirm = CF_RESIGN; gOverlay = OV_CONFIRM; clearSel(); break;
        case B_NEW:
            if (gM.mode == MODE_NET && !netConnected()) toast("НЕТ СВЯЗИ С СОПЕРНИКОМ");
            else if (gM.g.result == RES_NONE && !gM.g.moves.empty()) { gConfirm = CF_NEW; gOverlay = OV_CONFIRM; clearSel(); }
            else if (gM.mode == MODE_NET) netOffer("NEW");
            else restartSame();
            break;
        case B_DRAW: netOffer("DRAW"); break;
        case B_REVIEW:
        case B_RES_REVIEW: startReview(); break;
        case B_RV_FIRST: gRv.k = 0; break;
        case B_RV_PREV: gRv.k = std::max(0, gRv.k - 1); break;
        case B_RV_NEXT: gRv.k = std::min((int)gRv.g.moves.size(), gRv.k + 1); break;
        case B_RV_LAST: gRv.k = (int)gRv.g.moves.size(); break;
        case B_RV_MIST: gRv.k = rvNextMistake(gRv.k); break;
        case B_RV_DONE: leaveReview(); break;
        case B_LG_FIRST: gLGAuto = false; lessonGameShow(0); break;
        case B_LG_PREV: gLGAuto = false; lessonGameShow(gLGPly - 1); break;
        case B_LG_NEXT: gLGAuto = false; lessonGameShow(gLGPly + 1); break;
        case B_LG_LAST: gLGAuto = false; lessonGameShow((int)gLGMoves.size()); break;
        case B_LG_PLAY:
            if (gLGAuto) gLGAuto = false;
            else {
                if (gLGPly >= (int)gLGMoves.size()) lessonGameShow(0);
                gLGAuto = true;
                gLGNext = SDL_GetTicks() + 700;
            }
            break;
        case B_ARROWS:
            gArrowMode = !gArrowMode;
            clearSel();
            toast(gArrowMode ? "СТРЕЛКИ: ВЕДИТЕ ПАЛЬЦЕМ ПО ДОСКЕ" : "СТРЕЛКИ ВЫКЛЮЧЕНЫ");
            break;
        case B_NAV_FIRST: navTo(0); break;
        case B_NAV_PREV: navTo(viewPly() - 1); break;
        case B_NAV_NEXT: navTo(viewPly() + 1); break;
        case B_NAV_LAST: navTo((int)gM.g.moves.size()); break;
        case B_PLAY_NET:
            gScreen = SC_NET;
            gNetUI = NU_MENU;
            gNetMsg.clear();
            break;
        case B_NET_HOST:
            gNetMsg.clear();
            if (netHost()) gNetUI = NU_WAIT;
            else gNetMsg = "НЕ УДАЛОСЬ СОЗДАТЬ ИГРУ";
            break;
        case B_NET_JOIN:
            netCloseAll();
            netScanStart();
            gNetMsg.clear();
            gNetUI = NU_JOIN;
            break;
        case B_NET_CANCEL: netCancel(); break;
        case B_NET_MANUAL:
            if (gNetIpInput.empty()) gNetIpInput = gNetLastIp;
            gNetMsg.clear();
            gNetUI = NU_KEYPAD;
            break;
        case B_KEY0: case B_KEY1: case B_KEY2: case B_KEY3: case B_KEY4:
        case B_KEY5: case B_KEY6: case B_KEY7: case B_KEY8: case B_KEY9:
            if (gNetIpInput.size() < 15) gNetIpInput += (char)('0' + (id - B_KEY0));
            gNetMsg.clear();
            break;
        case B_KEY_DOT:
            if (gNetIpInput.size() < 15) gNetIpInput += '.';
            break;
        case B_KEY_DEL:
            if (!gNetIpInput.empty()) gNetIpInput.pop_back();
            break;
        case B_NET_GO:
            if (validIp(gNetIpInput)) {
                gNetLastIp = gNetIpInput;
                saveAll();
            }
            netJoinIp(gNetIpInput);
            break;
        case B_FOUND0: case B_FOUND1: case B_FOUND2: case B_FOUND3: case B_FOUND4: case B_FOUND5: {
            size_t i = (size_t)(id - B_FOUND0);
            if (i < gFound.size()) netJoinIp(gFound[i].ip);
            break;
        }
        case B_FLIP: gM.flip = !gM.flip; saveAll(); break;
        case B_MENU: leaveGameAsk(); break;
        case B_YES: {
            int c = gConfirm;
            gOverlay = OV_NONE;
            gConfirm = CF_NONE;
            if (c == CF_RESIGN) doResign();
            else if (c == CF_NEW && gM.mode == MODE_NET) netOffer("NEW");
            else if (c == CF_NEW) restartSame();
            else if (c == CF_NET_DRAW) {
                netSendLine("ACCEPT DRAW");
                if (gM.g.result == RES_NONE) {
                    gM.g.result = RES_DRAW;
                    gM.g.reason = R_AGREE;
                    onGameEnd();
                }
            } else if (c == CF_NET_NEW) {
                netSendLine("ACCEPT NEW");
                startNetMatch(gM.human ^ 1, gM.clockInit);
            } else if (c == CF_NET_LEAVE) {
                doResign();
                goMenu();
            } else if (c == CF_NET_LOST) {
                goMenu();
            }
            else if (c == CF_RESET) { gStats = Stats(); saveAll(); }
            break;
        }
        case B_NO: confirmCancel(); break;
        case B_RES_NEW:
            gOverlay = OV_NONE;
            if (gM.mode == MODE_NET) netOffer("NEW");
            else restartSame();
            break;
        case B_RES_VIEW: gOverlay = OV_NONE; break;
        case B_RES_MENU: gOverlay = OV_NONE; goMenu(); break;
        case B_PROMO_Q: case B_PROMO_R: case B_PROMO_B: case B_PROMO_N: {
            static const int T[4] = {eng::QUEEN, eng::ROOK, eng::BISHOP, eng::KNIGHT};
            int t = T[id - B_PROMO_Q];
            gOverlay = OV_NONE;
            for (auto m : gTargets)
                if (eng::mFrom(m) == gPromoFrom && eng::mTo(m) == gPromoTo && eng::mPromo(m) == t) {
                    playMove(m, true);
                    break;
                }
            break;
        }
        case B_RESET: gConfirm = CF_RESET; gOverlay = OV_CONFIRM; break;
        case B_LEARN: gScreen = SC_LEARN; break;
        case B_L_PREV:
            if (gLPg > 0) { openLesson(gLCh, gLPg - 1); gLScroll = 0; }
            break;
        case B_L_NEXT:
            if (gLPg < CHAPTERS[gLCh].n - 1) openLesson(gLCh, gLPg + 1);
            else if (gLCh < NCHAP - 1) openLesson(gLCh + 1, 0);
            else gScreen = SC_LEARN;
            gLScroll = 0;
            break;
        case B_L_MID: {
            int md = curPage().mode;
            if (md == LM_SHOW) gScreen = SC_LEARN;
            else if (md == LM_MOVES || gLStatus == 1) loadLessonPage(true);
            else gLShowHint = true;
            break;
        }
        default:
            if (id >= B_ED_PAL0 && id <= B_ED_PAL_END) {
                int i = id - B_ED_PAL0;
                gEdTool = eng::mkPiece(i / 6, ED_TYPES[i % 6]);
                break;
            }
            if (id >= B_CH0 && id < B_CH0 + NCHAP) {
                openLesson(id - B_CH0, 0);
                gLScroll = 0;
                gScreen = SC_LESSON;
            }
            break;
    }
}

static void onBack() {
    if (gOverlay != OV_NONE) {
        if (gOverlay == OV_PROMO) clearSel();
        confirmCancel();
        return;
    }
    switch (gScreen) {
        case SC_GAME: leaveGameAsk(); break;
        case SC_NET: netCancel(); break;
        case SC_REVIEW: leaveReview(); break;
        case SC_SETUP: gScreen = gCustomFen.empty() ? SC_MENU : SC_EDITOR; break;
        case SC_EDITOR: case SC_STATS: case SC_LEARN: gScreen = SC_MENU; break;
        case SC_LESSON: gScreen = SC_LEARN; break;
        default: gRunning = false; break;
    }
}

static const std::vector<Btn> &activeBtns() { return gOverlay != OV_NONE ? gOverBtns : gScreenBtns; }

static void pointerDown(float x, float y) {
    gPtr.down = true;
    gPtr.x = gPtr.sx = x;
    gPtr.y = gPtr.sy = y;
    gPtr.listDrag = false;
    gPtr.outside = false;
    gPressed = -1;
    for (auto &b : activeBtns())
        if (b.enabled && inRect(b.r, x, y)) {
            gPressed = b.id;
            return;
        }
    if (gOverlay != OV_NONE) {
        gPtr.outside = true;
        return;
    }
    if (gScreen == SC_EDITOR) {
        int s = edXYToSq(edLayout(), x, y);
        gEdDown = s >= 0;
        gEdFrom = s;
        gEdMoved = false;
        return;
    }
    if (gScreen == SC_REVIEW) {
        RvLayout RL = rvLayout();
        if (gRv.ready && y >= RL.listY && y < RL.listY + RL.listH) {
            gRvDrag = true;
            gRv.scrollStart = gRv.scroll;
        } else if (gRv.ready && x >= RL.bx && x < RL.bx + RL.S && y >= RL.by && y < RL.by + RL.S) {
            gRv.k = std::min((int)gRv.g.moves.size(), gRv.k + 1);  // нажатие на доску — следующий ход
        }
        return;
    }
    if (gScreen == SC_LESSON) {
        LessonLayout LL = lessonLayout();
        int ls = lessonXYToSq(LL, x, y);
        if (ls >= 0) lessonTap(ls);
        else if (x >= LL.textX && x < LL.textX + LL.textW && y >= LL.textY && y < LL.textY + LL.textH) {
            gLessonDrag = true;
            gLScrollStart = gLScroll;
        }
        return;
    }
    if (gScreen != SC_GAME) return;
    GameLayout L = gameLayout();
    if (x >= L.listX && x < L.listX + L.listW && y >= L.listY && y < L.listY + L.listH) {
        gPtr.listDrag = true;
        gPtr.listStart = gListScroll;
        return;
    }
    int s = xyToSq(L, x, y);
    if (s >= 0 && viewing()) {  // нажали на доску во время просмотра — к текущей позиции
        navTo((int)gM.g.moves.size());
        return;
    }
    if (s < 0) { clearSel(); return; }
    auto startArrow = [&]() {
        gArrowDrag = true;
        gArrowFrom = s;
    };
    if (gArrowMode || !canHumanMove()) {  // рисуем стрелку
        clearSel();
        startArrow();
        return;
    }
    const eng::Board &b = gM.g.cur;
    if (gSel >= 0 && isTarget(s)) {
        tryMove(gSel, s, true);
        return;
    }
    int p = b.sq[s];
    if (p && eng::pColor(p) == b.side) {
        gWasSelected = gSel == s;
        gSel = s;
        computeTargets();
        gDrag.active = true;
        gDrag.started = false;
        gDrag.sq = s;
        return;
    }
    clearSel();
    startArrow();  // от пустой клетки или фигуры соперника — стрелка
}

static void pointerMove(float x, float y) {
    gPtr.x = x;
    gPtr.y = y;
    if (!gPtr.down) return;
    if (gEdDown) {
        float dx = x - gPtr.sx, dy = y - gPtr.sy;
        float th = edLayout().cell * 0.2f;
        if (dx * dx + dy * dy > th * th) gEdMoved = true;
        return;
    }
    if (gRvDrag) {
        gRv.scroll = gRv.scrollStart - (y - gPtr.sy);
        return;
    }
    if (gLessonDrag) {
        gLScroll = gLScrollStart - (y - gPtr.sy);
        if (gLScroll < 0) gLScroll = 0;
        return;
    }
    if (gPtr.listDrag) {
        GameLayout L = gameLayout();
        float lineH = textH(L.tsSmall) + uiU() * 2.2f;
        gListScroll = gPtr.listStart + (int)std::lround((y - gPtr.sy) / lineH);
        if (gListScroll < 0) gListScroll = 0;
        return;
    }
    if (gDrag.active && !gDrag.started) {
        float dx = x - gPtr.sx, dy = y - gPtr.sy;
        GameLayout L = gameLayout();
        if (dx * dx + dy * dy > (L.cell * 0.18f) * (L.cell * 0.18f)) gDrag.started = true;
    }
}

static void pointerUp(float x, float y) {
    gPtr.x = x;
    gPtr.y = y;
    gPtr.down = false;
    if (gPressed >= 0) {
        int id = gPressed;
        gPressed = -1;
        // фигуру из палитры перетащили на доску
        if (gScreen == SC_EDITOR && id >= B_ED_PAL0 && id <= B_ED_PAL_END) {
            int sq = edXYToSq(edLayout(), x, y);
            if (sq >= 0) {
                int i = id - B_ED_PAL0;
                gEdTool = eng::mkPiece(i / 6, ED_TYPES[i % 6]);
                if (edPlace(sq, gEdTool, false)) playSound(SND_MOVE);
                return;
            }
        }
        for (auto &b : activeBtns())
            if (b.id == id && b.enabled && inRect(b.r, x, y)) {
                onButton(id);
                break;
            }
        return;
    }
    if (gPtr.outside) {
        gPtr.outside = false;
        if (gOverlay == OV_PROMO) { gOverlay = OV_NONE; clearSel(); }
        else if (gOverlay == OV_CONFIRM || gOverlay == OV_CHOOSE) confirmCancel();
        return;
    }
    if (gEdDown) {
        gEdDown = false;
        int to = edXYToSq(edLayout(), x, y);
        if (!gEdMoved) {
            if (to >= 0) edTap(to);
        } else if (gEdFrom >= 0 && gEdSq[gEdFrom]) {
            if (to < 0) {  // унесли фигуру за доску — удалить
                gEdSq[gEdFrom] = 0;
                playSound(SND_CAPTURE);
            } else {
                edMove(gEdFrom, to);
            }
        } else if (to >= 0) {
            edTap(to);
        }
        gEdFrom = -1;
        return;
    }
    if (gRvDrag) {
        gRvDrag = false;
        float dx = x - gPtr.sx, dy = y - gPtr.sy;
        if (dx * dx + dy * dy < uiU() * uiU() * 9) {
            int i = rvListHit(x, y);
            if (i >= 0) {
                gRv.k = i + 1;
                playSound(SND_CLICK);
            }
        }
        return;
    }
    if (gLessonDrag) { gLessonDrag = false; return; }
    if (gPtr.listDrag) {
        gPtr.listDrag = false;
        float dx = x - gPtr.sx, dy = y - gPtr.sy;
        if (gScreen == SC_GAME && dx * dx + dy * dy < uiU() * uiU() * 9) {
            int ply = listHit(gameLayout(), x, y);
            if (ply >= 0) {
                navTo(ply + 1);
                playSound(SND_CLICK);
            }
        }
        return;
    }
    if (gScreen == SC_GAME && gArrowDrag) {
        gArrowDrag = false;
        int to = xyToSq(gameLayout(), x, y);
        if (to >= 0 && to != gArrowFrom) toggleArrow(gArrowFrom, to);
        else if (to >= 0 && to == gArrowFrom && gArrowMode) toggleCircle(to);
        else if (to >= 0 && to == gArrowFrom && !gUArrows.empty() && !gArrowMode) clearUserMarks();  // тап — стереть
        return;
    }
    if (gScreen == SC_GAME && gDrag.active) {
        gDrag.active = false;
        if (gDrag.started) {
            gDrag.started = false;
            GameLayout L = gameLayout();
            int s = xyToSq(L, x, y);
            if (s >= 0 && s != gDrag.sq && isTarget(s)) tryMove(gDrag.sq, s, false);
        } else if (gWasSelected) {
            clearSel();
        }
    }
}

// Размер окна (SDL_GetWindowSize) и реальная область рисования на некоторых
// телефонах отличаются (строка состояния, вырез камеры). Рисуем и пересчитываем
// касания по реальной области рисования, иначе нажатие «съезжает».
static float gMouseSX = 1.0f, gMouseSY = 1.0f;  // окно -> пиксели рисования (для мыши)
static void updateSize() {
    int w = 0, h = 0;
    SDL_GetWindowSize(gWin, &w, &h);
    int ow = 0, oh = 0;
    if (R && SDL_GetRendererOutputSize(R, &ow, &oh) == 0 && ow > 0 && oh > 0) {
        if (ow != gW || oh != gH) gTexDirty = true;
        gW = ow;
        gH = oh;
        gMouseSX = w > 0 ? (float)ow / w : 1.0f;
        gMouseSY = h > 0 ? (float)oh / h : 1.0f;
    } else if (w > 0 && h > 0) {
        gW = w;
        gH = h;
        gMouseSX = gMouseSY = 1.0f;
    }
}

static int gDirty = 2;

static void handleEvent(const SDL_Event &e) {
    gDirty = 3;
    switch (e.type) {
        case SDL_QUIT: gRunning = false; break;
        case SDL_APP_TERMINATING: saveAll(); gRunning = false; break;
        case SDL_APP_WILLENTERBACKGROUND: saveAll(); break;
        case SDL_APP_DIDENTERBACKGROUND: gPaused = true; break;
        case SDL_APP_DIDENTERFOREGROUND:
            gPaused = false;
            gLastTick = SDL_GetTicks();
            gTexDirty = true;
            updateSize();
            break;
        case SDL_WINDOWEVENT:
            if (e.window.event == SDL_WINDOWEVENT_SIZE_CHANGED || e.window.event == SDL_WINDOWEVENT_RESIZED) updateSize();
            if (e.window.event == SDL_WINDOWEVENT_FOCUS_GAINED || e.window.event == SDL_WINDOWEVENT_SHOWN) gLastTick = SDL_GetTicks();
            break;
        case SDL_RENDER_TARGETS_RESET:
        case SDL_RENDER_DEVICE_RESET: gTexDirty = true; break;
        case SDL_KEYDOWN:
            if (e.key.repeat) break;
            if (e.key.keysym.sym == SDLK_AC_BACK || e.key.keysym.sym == SDLK_ESCAPE) onBack();
            if (gScreen == SC_GAME && gOverlay == OV_NONE) {
                if (e.key.keysym.sym == SDLK_LEFT) navTo(viewPly() - 1);
                if (e.key.keysym.sym == SDLK_RIGHT) navTo(viewPly() + 1);
                if (e.key.keysym.sym == SDLK_HOME || e.key.keysym.sym == SDLK_UP) navTo(0);
                if (e.key.keysym.sym == SDLK_END || e.key.keysym.sym == SDLK_DOWN) navTo((int)gM.g.moves.size());
            }
#if !defined(__ANDROID__)
            if (e.key.keysym.sym == SDLK_F11) {
                Uint32 fl = SDL_GetWindowFlags(gWin);
                SDL_SetWindowFullscreen(gWin, (fl & SDL_WINDOW_FULLSCREEN_DESKTOP) ? 0 : SDL_WINDOW_FULLSCREEN_DESKTOP);
                updateSize();
            }
#endif
            break;
        case SDL_FINGERDOWN:
            if (!gPtr.down) {
                gPtr.finger = true;
                gPtr.fid = e.tfinger.fingerId;
                pointerDown(e.tfinger.x * gW, e.tfinger.y * gH);
            }
            break;
        case SDL_FINGERMOTION:
            if (gPtr.down && gPtr.finger && gPtr.fid == e.tfinger.fingerId) pointerMove(e.tfinger.x * gW, e.tfinger.y * gH);
            break;
        case SDL_FINGERUP:
            if (gPtr.down && gPtr.finger && gPtr.fid == e.tfinger.fingerId) pointerUp(e.tfinger.x * gW, e.tfinger.y * gH);
            break;
        case SDL_MOUSEBUTTONDOWN:
            if (e.button.which == SDL_TOUCH_MOUSEID) break;
            if (e.button.button == SDL_BUTTON_RIGHT && gScreen == SC_GAME && gOverlay == OV_NONE && !gPtr.down) {
                int sq = xyToSq(gameLayout(), e.button.x * gMouseSX, e.button.y * gMouseSY);
                if (sq >= 0) {
                    clearSel();
                    gArrowDrag = true;
                    gArrowFrom = sq;
                    gPtr.x = e.button.x * gMouseSX;
                    gPtr.y = e.button.y * gMouseSY;
                }
                break;
            }
            if (e.button.button != SDL_BUTTON_LEFT) break;
            if (!gPtr.down) {
                gPtr.finger = false;
                pointerDown(e.button.x * gMouseSX, e.button.y * gMouseSY);
            }
            break;
        case SDL_MOUSEMOTION:
            if (e.motion.which == SDL_TOUCH_MOUSEID) break;
            if (gArrowDrag && !gPtr.down) {
                gPtr.x = e.motion.x * gMouseSX;
                gPtr.y = e.motion.y * gMouseSY;
                break;
            }
            if (!gPtr.finger || !gPtr.down) pointerMove(e.motion.x * gMouseSX, e.motion.y * gMouseSY);
            break;
        case SDL_MOUSEBUTTONUP:
            if (e.button.which == SDL_TOUCH_MOUSEID) break;
            if (e.button.button == SDL_BUTTON_RIGHT && gArrowDrag) {
                gArrowDrag = false;
                int to = xyToSq(gameLayout(), e.button.x * gMouseSX, e.button.y * gMouseSY);
                if (to >= 0 && to != gArrowFrom) toggleArrow(gArrowFrom, to);
                else if (to >= 0) toggleCircle(to);
                break;
            }
            if (e.button.button != SDL_BUTTON_LEFT) break;
            if (gPtr.down && !gPtr.finger) pointerUp(e.button.x * gMouseSX, e.button.y * gMouseSY);
            break;
        case SDL_MOUSEWHEEL:
            if (gScreen == SC_GAME) gListScroll += e.wheel.y > 0 ? 1 : (e.wheel.y < 0 ? -1 : 0);
            if (gListScroll < 0) gListScroll = 0;
            break;
        default: break;
    }
}

static void update() {
    netPoll();
    pollReview();
    Uint32 now = SDL_GetTicks();
    Uint32 dt = now - gLastTick;
    gLastTick = now;
    if (dt > 1000) dt = 1000;  // защита от скачков после паузы
    if (!gAnims.empty() && animT() >= 1.0f) gAnims.clear();
    if (gAnims.empty() && gM.g.result == RES_NONE) gViewSide = gM.g.cur.side;
    if (gScreen == SC_GAME && gM.active) {
        // ход бота
        if (gThread && gJob && gJob->done.load() && now - gBotStart >= 350) {
            SDL_WaitThread(gThread, nullptr);
            gThread = nullptr;
            eng::Move m = gJob->result;
            delete gJob;
            gJob = nullptr;
            if (m && gM.g.result == RES_NONE) playMove(m, true);
        }
        // часы
        if (gM.clockInit > 0 && gM.g.result == RES_NONE && !gPaused && !gM.g.moves.empty()) {
            int side = gM.g.cur.side;
            if (gM.mode == MODE_NET) {
                // свои часы решают сами; чужим даём запас на задержку сети
                if (netConnected()) {
                    gM.tLeft[side] -= dt;
                    if (side == gM.human && gM.tLeft[side] <= 0) {
                        netSendLine("TIMEOUT");
                        onTimeout(side);
                    } else if (side != gM.human && gM.tLeft[side] <= -8000) {
                        onTimeout(side);
                    }
                }
            } else {
                gM.tLeft[side] -= dt;
                if (gM.tLeft[side] <= 0) onTimeout(side);
            }
        }
        if (gResultPending && gAnims.empty() && now >= gResultAt) {
            gResultPending = false;
            if (gScreen == SC_GAME && gM.g.result != RES_NONE) gOverlay = OV_RESULT;
        }
    }
    if (gScreen == SC_LESSON && gLResetAt && now >= gLResetAt) lessonUndoWrong();
    if (gScreen == SC_LESSON && gLReplyAt && now >= gLReplyAt) lessonReply();
    if (gScreen == SC_LESSON && gLGAuto && now >= gLGNext) {
        if (gLGPly < (int)gLGMoves.size()) {
            lessonGameShow(gLGPly + 1);
            playSound(gLB.inCheck(gLB.side) ? SND_CHECK : SND_MOVE);
            gLGNext = now + 1500;
        }
        if (gLGPly >= (int)gLGMoves.size()) gLGAuto = false;
    }
    buildScreenButtons();
    buildOverlayButtons();
}

static bool needsAnimation() {
    if (gPtr.down || gArrowDrag || !gAnims.empty() || botThinking() || gResultPending || gLResetAt || gLReplyAt || gLGAuto) return true;
    if (gScreen == SC_NET || SDL_GetTicks() < gToastUntil || gRvJob) return true;
    if (gScreen == SC_GAME && gM.clockInit > 0 && gM.g.result == RES_NONE && !gM.g.moves.empty()) return true;
    return false;
}

// Сохранение в момент ухода в фон: вызывается сразу из потока Android
static int SDLCALL eventFilter(void *, SDL_Event *e) {
    if (e->type == SDL_APP_WILLENTERBACKGROUND || e->type == SDL_APP_TERMINATING || e->type == SDL_APP_LOWMEMORY) {
        if (gLock) SDL_LockMutex(gLock);
        saveAll();
        if (gLock) SDL_UnlockMutex(gLock);
    }
    return 1;
}

// =====================================================================
//                       САМОПРОВЕРКА (ПК)
// =====================================================================
static int runPerft(int maxDepth) {
    eng::Board b;
    b.setStart();
    static const unsigned long long EXP[7] = {1, 20, 400, 8902, 197281, 4865609, 119060324};
    int bad = 0;
    for (int d = 1; d <= maxDepth && d <= 6; d++) {
        Uint32 t0 = SDL_GetTicks();
        unsigned long long n = eng::perft(b, d);
        Uint32 t1 = SDL_GetTicks();
        printf("perft %d = %llu  (ожидается %llu)  %s  %u мс\n", d, n, EXP[d], n == EXP[d] ? "OK" : "ОШИБКА",
               (unsigned)(t1 - t0));
        if (n != EXP[d]) bad++;
    }
    return bad ? 1 : 0;
}

static int selfTest() {
    struct T { const char *fen; int d; unsigned long long n; };
    const T tests[] = {
        {"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 4, 197281ULL},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 3, 97862ULL},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 5, 674624ULL},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 4, 422333ULL},
        {"rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 3, 62379ULL},
        {"r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", 3, 89890ULL},
    };
    int bad = 0;
    for (auto &t : tests) {
        eng::Board b;
        b.setFEN(t.fen);
        unsigned long long n = eng::perft(b, t.d);
        printf("%-72s d%d = %llu %s\n", t.fen, t.d, n, n == t.n ? "OK" : "ОШИБКА");
        if (n != t.n) bad++;
    }
    // хеш после случайной партии совпадает с пересчитанным
    {
        eng::Board b;
        b.setStart();
        uint32_t rng = 12345;
        for (int i = 0; i < 4000; i++) {
            eng::MoveList ml;
            b.genLegal(ml);
            if (!ml.n || b.half >= 100) { b.setStart(); continue; }
            eng::Undo u;
            b.make(ml.m[eng::xrand(rng) % (uint32_t)ml.n], u);
            if (b.hash != b.computeHash()) { printf("ОШИБКА хеша на ходу %d\n", i); bad++; break; }
        }
    }
    // запись ходов
    {
        Game g;
        g.reset();
        const char *uci[] = {"e2e4", "e7e5", "g1f3", "b8c6", "f1c4", "g8f6", "f3g5", "d7d5", "e4d5", "f6d5", "g5f7", "e8f7", "d1f3"};
        for (auto u : uci) {
            eng::MoveList ml;
            g.cur.genLegal(ml);
            for (int k = 0; k < ml.n; k++)
                if (eng::toUCI(ml.m[k]) == u) { g.play(ml.m[k]); break; }
        }
        std::string all;
        for (auto &s : g.san) all += s + " ";
        printf("Запись: %s\n", all.c_str());
        if (g.san.size() != 13 || g.san[2] != "Кf3" || g.san[11] != "Крxf7" || g.san[12] != "Фf3+") { printf("ОШИБКА записи\n"); bad++; }
    }
    // мат в один ход находит бот всех уровней 3..5
    {
        eng::ttInit(18);
        eng::Board b;
        b.setFEN("6k1/5ppp/8/8/8/8/5PPP/3R2K1 w - - 0 1");
        std::vector<uint64_t> h(1, b.hash);
        for (int lv = 3; lv <= 5; lv++) {
            eng::Move m = eng::think(b, h, lv, 1500, 20, 777, nullptr);
            printf("Уровень %d: %s %s\n", lv, eng::toUCI(m).c_str(), eng::toUCI(m) == "d1d8" ? "OK" : "ОШИБКА");
            if (eng::toUCI(m) != "d1d8") bad++;
        }
    }
    printf(bad ? "САМОПРОВЕРКА: ЕСТЬ ОШИБКИ\n" : "САМОПРОВЕРКА: ВСЁ ВЕРНО\n");
    return bad ? 1 : 0;
}

// =====================================================================
//                              MAIN
// =====================================================================
static bool appInit() {
    SDL_SetHint(SDL_HINT_ORIENTATIONS, "Portrait");
    SDL_SetHint("SDL_ANDROID_TRAP_BACK_BUTTON", "1");
    SDL_SetHint(SDL_HINT_TOUCH_MOUSE_EVENTS, "0");
    SDL_SetHint(SDL_HINT_MOUSE_TOUCH_EVENTS, "0");
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS | SDL_INIT_TIMER) != 0) {
        SDL_Log("SDL_Init: %s", SDL_GetError());
        return false;
    }
    gLock = SDL_CreateMutex();
#if defined(__ANDROID__)
    gWin = SDL_CreateWindow("Шахматы", SDL_WINDOWPOS_UNDEFINED, SDL_WINDOWPOS_UNDEFINED, 0, 0,
                            SDL_WINDOW_FULLSCREEN_DESKTOP | SDL_WINDOW_SHOWN);
#else
    int ww = 540, wh = 960;
    SDL_Rect ub;
    if (SDL_GetDisplayUsableBounds(0, &ub) == 0 && ub.h > 200) {
        wh = std::min(960, (int)(ub.h * 0.92f));
        ww = wh * 9 / 16;
    }
    gWin = SDL_CreateWindow("Шахматы", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, ww, wh,
                            SDL_WINDOW_RESIZABLE | SDL_WINDOW_SHOWN);
#endif
    if (!gWin) {
        SDL_Log("SDL_CreateWindow: %s", SDL_GetError());
        return false;
    }
    R = SDL_CreateRenderer(gWin, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC | SDL_RENDERER_TARGETTEXTURE);
    if (!R) R = SDL_CreateRenderer(gWin, -1, SDL_RENDERER_ACCELERATED);
    if (!R) R = SDL_CreateRenderer(gWin, -1, SDL_RENDERER_SOFTWARE);
    if (!R) {
        SDL_Log("SDL_CreateRenderer: %s", SDL_GetError());
        return false;
    }
    SDL_SetRenderDrawBlendMode(R, SDL_BLENDMODE_BLEND);
    updateSize();
    fontInit();
    geoInit();
    vpiecesInit();
    eng::ttInit(19);
    initSavePath();
    loadAll();
    audioInit();
    SDL_SetEventFilter(eventFilter, nullptr);
    gLastTick = SDL_GetTicks();
    gScreen = SC_MENU;
    buildScreenButtons();
    return true;
}

static void appFrame() {
    SDL_Event e;
    if (!needsAnimation() && gDirty <= 0 && !gPaused) {
        if (SDL_WaitEventTimeout(&e, netBusy() ? 30 : 500)) {
            SDL_LockMutex(gLock);
            handleEvent(e);
            SDL_UnlockMutex(gLock);
        }
    }
    while (SDL_PollEvent(&e)) {
        SDL_LockMutex(gLock);
        handleEvent(e);
        SDL_UnlockMutex(gLock);
    }
    if (gPaused) {
        SDL_LockMutex(gLock);
        gLastTick = SDL_GetTicks();
        netPoll();  // держим соединение, пока приложение свёрнуто
        SDL_UnlockMutex(gLock);
        if (SDL_WaitEventTimeout(&e, 200)) {
            SDL_LockMutex(gLock);
            handleEvent(e);
            SDL_UnlockMutex(gLock);
        }
        return;
    }
    SDL_LockMutex(gLock);
    updateSize();  // размер мог поменяться (поворот, строка состояния, вырез)
    SDL_RenderSetViewport(R, nullptr);
    update();
    render();
    SDL_UnlockMutex(gLock);
    SDL_RenderPresent(R);
    if (gDirty > 0) gDirty--;
}

static void appQuit() {
    cancelBot();
    cancelReview();
    if (gM.mode == MODE_NET) netLeave(true);
    netCloseAll();
    saveAll();
    if (gAudioOk) SDL_CloseAudio();
    freePieceTex();
    if (R) SDL_DestroyRenderer(R);
    if (gWin) SDL_DestroyWindow(gWin);
    SDL_SetEventFilter(nullptr, nullptr);
    if (gLock) SDL_DestroyMutex(gLock);
    gLock = nullptr;
    SDL_Quit();
}

int main(int argc, char **argv) {
    eng::init();
    if (argc > 1 && strcmp(argv[1], "--perft") == 0) return runPerft(argc > 2 ? atoi(argv[2]) : 4);
    if (argc > 1 && strcmp(argv[1], "--selftest") == 0) return selfTest();
    if (!appInit()) return 1;
    while (gRunning) appFrame();
    appQuit();
    return 0;
}
