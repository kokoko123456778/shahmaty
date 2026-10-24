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
    Move m[256];
    int n = 0;
    void add(Move x) { m[n++] = x; }
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

    Searcher() {
        memset(killers, 0, sizeof(killers));
        memset(hist, 0, sizeof(hist));
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
        int sc[256];
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

        TTE &e = g_tt[b.hash & g_ttMask];
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
        int sc[256];
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

}  // namespace eng

// =====================================================================
//                           ПАРТИЯ
// =====================================================================
enum { RES_NONE = 0, RES_WHITE = 1, RES_BLACK = 2, RES_DRAW = 3 };
enum { R_NONE = 0, R_MATE, R_STALEMATE, R_RESIGN, R_TIME, R_FIFTY, R_REPEAT, R_MATERIAL };

struct Game {
    eng::Board cur;
    std::vector<eng::Board> before;
    std::vector<eng::Move> moves;
    std::vector<std::string> san;
    std::vector<uint64_t> hashes;
    int result = RES_NONE, reason = R_NONE, loser = -1;

    void reset() {
        cur.setStart();
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
    {'g', {".....", ".####", "#...#", "#...#", ".####", "....#", ".###."}},
    {'h', {"#....", "#....", "####.", "#...#", "#...#", "#...#", "#...#"}},
    {'x', {".....", ".....", "#...#", ".#.#.", "..#..", ".#.#.", "#...#"}},
    // --- знаки ---
    {'+', {".....", "..#..", "..#..", "#####", "..#..", "..#..", "....."}},
    {'#', {".#.#.", ".#.#.", "#####", ".#.#.", "#####", ".#.#.", ".#.#."}},
    {'-', {".....", ".....", ".....", "####.", ".....", ".....", "....."}},
    {'=', {".....", ".....", "####.", ".....", "####.", ".....", "....."}},
    {'.', {".....", ".....", ".....", ".....", ".....", "##...", "##..."}},
    {',', {".....", ".....", ".....", ".....", "##...", ".#...", "#...."}},
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
    if (!gUseTex || !SDL_RenderTargetSupported(R)) {
        gUseTex = false;
        return;
    }
    int ts = std::max(32, std::min(512, cell * 2));
    for (int c = 0; c < 2; c++)
        for (int t = 1; t <= 6; t++) {
            SDL_Texture *tx = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA8888, SDL_TEXTUREACCESS_TARGET, ts, ts);
            if (!tx) { gUseTex = false; freePieceTex(); SDL_SetRenderTarget(R, nullptr); return; }
            SDL_SetTextureBlendMode(tx, SDL_BLENDMODE_BLEND);
            SDL_SetTextureScaleMode(tx, SDL_ScaleModeLinear);
            if (SDL_SetRenderTarget(R, tx) != 0) {
                SDL_DestroyTexture(tx);
                gUseTex = false;
                freePieceTex();
                SDL_SetRenderTarget(R, nullptr);
                return;
            }
            SDL_SetRenderDrawBlendMode(R, SDL_BLENDMODE_NONE);
            SDL_SetRenderDrawColor(R, 0, 0, 0, 0);
            SDL_RenderClear(R);
            SDL_SetRenderDrawBlendMode(R, SDL_BLENDMODE_BLEND);
            drawPieceShape(c, t, 0, 0, (float)ts, true);
            gPieceTex[c][t] = tx;
        }
    SDL_SetRenderTarget(R, nullptr);
    SDL_SetRenderDrawBlendMode(R, SDL_BLENDMODE_BLEND);
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
enum { SC_MENU, SC_SETUP, SC_GAME, SC_STATS };
enum { OV_NONE, OV_PROMO, OV_CONFIRM, OV_RESULT };
enum { CF_NONE, CF_RESIGN, CF_NEW, CF_RESET };
enum { MODE_BOT = 0, MODE_TWO = 1 };

struct Settings {
    int level = 2;
    int color = 0;  // 0 белые, 1 чёрные, 2 случайно
    int clock = 0;  // 0 нет, 1 = 5 мин, 2 = 10, 3 = 15
};
struct Stats {
    int wins = 0, losses = 0, draws = 0, two = 0;
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

struct Pointer {
    bool down = false;
    bool finger = false;
    SDL_FingerID fid = 0;
    float x = 0, y = 0, sx = 0, sy = 0;
    bool listDrag = false;
    int listStart = 0;
    bool outside = false;
} gPtr;

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
    snprintf(buf, sizeof buf, "STATS %d %d %d %d\n", gStats.wins, gStats.losses, gStats.draws, gStats.two);
    s += buf;
    snprintf(buf, sizeof buf, "SET %d %d %d %d\n", gSet.level, gSet.color, gSet.clock, gSoundOn);
    s += buf;
    snprintf(buf, sizeof buf, "MATCH %d %d %d %d %d %lld %lld %d %d %d %d %d\n", gM.active ? 1 : 0, gM.mode, gM.human,
             gM.level, gM.clockInit, gM.tLeft[0], gM.tLeft[1], gM.flip ? 1 : 0, gM.recorded ? 1 : 0, gM.g.result,
             gM.g.reason, gM.g.loser);
    s += buf;
    s += "MOVES";
    for (auto m : gM.g.moves) s += " " + eng::toUCI(m);
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
    std::string movesLine;
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
            if (sscanf(line.c_str() + 6, "%d %d %d %d", &st.wins, &st.losses, &st.draws, &st.two) == 4) gStats = st;
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
        } else if (line.compare(0, 5, "MOVES") == 0) {
            movesLine = line.substr(5);
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
    gM.g.reset();
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
    gJob->gamePly = (int)gM.g.moves.size();
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
    gM.g.play(m);
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

static void newMatch(int mode, int level, int colorChoice, int clockChoice) {
    cancelBot();
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
    gM.g.reset();
    gViewSide = eng::WHITE;
    clearSel();
    gAnims.clear();
    gResultPending = false;
    gOverlay = OV_NONE;
    gListScroll = 0;
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
    newMatch(gM.mode, gM.level, colorChoice, clockChoice);
}

static void doUndo() {
    if (!gM.active) return;
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
    playSound(SND_CLICK);
    saveAll();
    startBot();
}

static bool canUndo() {
    if (!gM.active || gM.g.moves.empty()) return false;
    if (gM.mode == MODE_BOT) {
        if (gM.g.result != RES_NONE) return false;
        if (botThinking()) return true;
        if (gM.g.cur.side == gM.human) {
            // нельзя отменить первый ход бота, если ходов больше нет
            return !(gM.g.moves.size() == 1 && gM.human == eng::BLACK);
        }
        return true;
    }
    return true;
}

static void doResign() {
    if (!gM.active || gM.g.result != RES_NONE) return;
    int loser = gM.mode == MODE_BOT ? gM.human : gM.g.cur.side;
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
    if (gScreen != SC_GAME || !gM.active || gM.g.result != RES_NONE || gOverlay != OV_NONE) return false;
    if (gM.mode == MODE_BOT) return !botThinking() && gM.g.cur.side == gM.human;
    return true;
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
    B_RESET
};
enum { ST_NORMAL, ST_PRIMARY, ST_DANGER, ST_SEG, ST_TOOL };
enum { IC_NONE, IC_UNDO, IC_FLAG, IC_PLUS, IC_FLIP, IC_MENU };

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

struct GameLayout {
    float top, pad, barH, btnH, bx, by, cell, S, topBarY, botBarY, listX, listY, listW, listH, btnY;
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
    L.ts = uiTS();
    L.tsSmall = std::max(1, (int)std::lround(U * 0.42f));
    return L;
}

static bool whiteBottom() {
    bool base = gM.mode == MODE_BOT ? gM.human == eng::WHITE : gViewSide == eng::WHITE;
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
    int rows = m.cont ? 5 : 4;
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
        gScreenBtns.push_back(mkBtn(x, y, bw, bh, B_PLAY_TWO, "ИГРА ВДВОЁМ", ST_NORMAL, bts));
        y += bh + gap;
        gScreenBtns.push_back(mkBtn(x, y, bw, bh, B_STATS, "СТАТИСТИКА", ST_NORMAL, bts));
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
    } else if (gScreen == SC_STATS) {
        float bw = std::min(W * 0.82f, U * 82.0f), x = (W - bw) * 0.5f, bh = std::max(40.0f, U * 14.0f);
        float yb = H - U * 6 - bh;
        gScreenBtns.push_back(mkBtn(x, yb - bh - U * 3, bw, bh, B_RESET, "СБРОСИТЬ", ST_DANGER, ts + 1));
        gScreenBtns.push_back(mkBtn(x, yb, bw, bh, B_BACK, "НАЗАД", ST_NORMAL, ts + 1));
    } else if (gScreen == SC_GAME) {
        GameLayout L = gameLayout();
        float gap = L.pad * 0.5f;
        float bw = (L.listW - 4 * gap) / 5;
        const char *lb[5] = {"ОТМЕНА", "СДАТЬСЯ", "НОВАЯ", "ПОВОРОТ", "МЕНЮ"};
        int ids[5] = {B_UNDO, B_RESIGN, B_NEW, B_FLIP, B_MENU};
        int ic[5] = {IC_UNDO, IC_FLAG, IC_PLUS, IC_FLIP, IC_MENU};
        int lts = L.tsSmall;
        for (int i = 0; i < 5; i++) lts = std::min(lts, fitScale(lb[i], bw * 0.9f, L.tsSmall));
        for (int i = 0; i < 5; i++) {
            Btn b = mkBtn(L.listX + i * (bw + gap), L.btnY, bw, L.btnH, ids[i], lb[i], ST_TOOL, lts);
            b.icon = ic[i];
            if (ids[i] == B_UNDO) b.enabled = canUndo();
            if (ids[i] == B_RESIGN) b.enabled = gM.g.result == RES_NONE;
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
        gOverBtns.push_back(mkBtn(p.x + U * 4, y, bw, bh, B_YES, "ДА", gConfirm == CF_NEW ? ST_PRIMARY : ST_DANGER, ts + 1));
        gOverBtns.push_back(mkBtn(p.x + p.w - U * 4 - bw, y, bw, bh, B_NO, "НЕТ", ST_NORMAL, ts + 1));
    } else if (gOverlay == OV_RESULT) {
        Panel p = overlayPanel(106);
        float bw = p.w - U * 10, bh = std::max(38.0f, U * 12.5f), gap = U * 2.5f;
        float x = p.x + U * 5;
        float y = p.y + p.h - U * 5 - 3 * bh - 2 * gap;
        gOverBtns.push_back(mkBtn(x, y, bw, bh, B_RES_NEW, "НОВАЯ ПАРТИЯ", ST_PRIMARY, ts + 1));
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
        case ST_TOOL: top = C(52, 63, 82); bot = C(38, 47, 62); border = C(76, 90, 114); break;
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
    if (b.style == ST_TOOL) {
        float is = b.r.h * 0.36f;
        drawIcon(b.icon, cx, b.r.y + b.r.h * 0.36f + off, is, tc);
        text(b.label, cx, b.r.y + b.r.h * 0.70f + off, b.ts, tc, 1, false);
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
    if (gSetupMode == MODE_TWO) {
        int s2 = fitScale("ДОСКА ПОВОРАЧИВАЕТСЯ ПОСЛЕ ХОДА", W * 0.9f, ts);
        text("ДОСКА ПОВОРАЧИВАЕТСЯ ПОСЛЕ ХОДА", W * 0.5f, top + U * 6 + textH(tts) + U * 3, s2, COL_DIM, 1, false);
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
    Row rows[6] = {
        {"ПОБЕДЫ", std::to_string(gStats.wins), C(120, 214, 120)},
        {"ПОРАЖЕНИЯ", std::to_string(gStats.losses), C(232, 110, 100)},
        {"НИЧЬИ", std::to_string(gStats.draws), C(200, 200, 210)},
        {"ВСЕГО С БОТОМ", std::to_string(total), COL_TEXT},
        {"РЕЗУЛЬТАТ", std::to_string(pct) + "%", COL_GOLD},
        {"ПАРТИЙ ВДВОЁМ", std::to_string(gStats.two), COL_TEXT},
    };
    float ph = lh * 6 + U * 6;
    fillRRect(px, py, pw, ph, U * 3, C(36, 46, 62, 230));
    float y = py + U * 3 + (lh - textH(ts + 1)) * 0.5f;
    for (int i = 0; i < 6; i++) {
        int sc = fitScale(rows[i].l, pw * 0.65f, ts + 1);
        text(rows[i].l, px + U * 4, y, sc, COL_DIM, 0, false);
        text(rows[i].v, px + pw - U * 4, y, ts + 1, rows[i].c, 2);
        if (i < 5) fillRect(px + U * 4, y + lh - (lh - textH(ts + 1)) * 0.5f - 1, pw - U * 8, 1, C(255, 255, 255, 18));
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
    int cnt[2][7] = {{0}};
    const eng::Board &b = gM.g.cur;
    for (int s = 0; s < 64; s++)
        if (b.sq[s]) cnt[eng::pColor(b.sq[s])][eng::pType(b.sq[s])]++;
    int opp = color ^ 1;
    capt.clear();
    for (int t = eng::QUEEN; t >= eng::PAWN; t--) {
        int miss = START[t] - cnt[opp][t];
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

static void drawBoard(const GameLayout &L) {
    float U = uiU();
    float fr = std::max(3.0f, L.cell * 0.09f);
    fillRRect(L.bx - fr, L.by - fr, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, C(0, 0, 0, 90));
    fillRRect(L.bx - fr, L.by - fr + 1, L.S + 2 * fr, L.S + 2 * fr, fr * 1.2f, vgrad(C(96, 66, 42), C(58, 38, 24), L.by, L.by + L.S));
    const eng::Board &b = gM.g.cur;
    for (int s = 0; s < 64; s++) {
        float x, y;
        sqToXY(L, s, x, y);
        bool light = ((s & 7) + (s >> 3)) & 1;
        Col c = light ? COL_LIGHT : COL_DARK;
        fillRect(x, y, L.cell, L.cell, c);
    }
    // последний ход
    if (!gM.g.moves.empty()) {
        eng::Move m = gM.g.moves.back();
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
    bool animating = at < 1.0f;
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
    if (g.result != RES_NONE) {
        c = COL_GOLD;
        if (g.result == RES_DRAW) return "НИЧЬЯ";
        int win = g.result == RES_WHITE ? eng::WHITE : eng::BLACK;
        if (gM.mode == MODE_BOT) return win == gM.human ? "ВЫ ПОБЕДИЛИ!" : "ВЫ ПРОИГРАЛИ";
        return "ПОБЕДИЛИ " + sideName(win, true);
    }
    bool chk = g.cur.inCheck(g.cur.side);
    std::string s;
    if (gM.mode == MODE_BOT) {
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

static void drawMoveList(const GameLayout &L) {
    float U = uiU();
    fillRRect(L.listX, L.listY, L.listW, L.listH, U * 2.2f, C(22, 28, 40, 220));
    int ts = L.ts;
    Col sc;
    std::string st = statusText(sc);
    float sy = L.listY + U * 2.2f;
    int sts = fitScale(st, L.listW - U * 6, ts);
    text(st, L.listX + U * 3, sy, sts, sc);
    std::string cnt = gM.g.moves.empty() ? "" : ("ХОД " + std::to_string((gM.g.moves.size() + 1) / 2));
    if (!cnt.empty() && textW(st, sts) + textW(cnt, L.tsSmall) + U * 10 < L.listW)
        text(cnt, L.listX + L.listW - U * 3, sy + textH(sts) - textH(L.tsSmall), L.tsSmall, COL_DIM, 2, false);
    float y0 = sy + textH(sts) + U * 2.5f;
    fillRect(L.listX + U * 3, y0 - U * 1.2f, L.listW - U * 6, 1, C(255, 255, 255, 25));
    int lts = L.tsSmall;
    float lineH = textH(lts) + U * 2.2f;
    int rowsVis = (int)((L.listY + L.listH - y0 - U * 1.0f) / lineH);
    if (rowsVis < 1) return;
    int nPairs = (int)(gM.g.san.size() + 1) / 2;
    float numW = (float)textW("000.", lts);
    float plyW = (float)textW("Крxe8+ ", lts);
    float pairW = numW + 2 * plyW + U * 3;
    int cols = std::max(1, (int)((L.listW - U * 4) / pairW));
    int totalRows = (nPairs + cols - 1) / cols;
    int maxScroll = std::max(0, totalRows - rowsVis);
    if (gListScroll > maxScroll) gListScroll = maxScroll;
    if (gListScroll < 0) gListScroll = 0;
    int firstRow = std::max(0, totalRows - rowsVis - gListScroll);
    float colW = (L.listW - U * 4) / cols;
    int lastPly = (int)gM.g.san.size() - 1;
    for (int r = 0; r < rowsVis; r++) {
        int row = firstRow + r;
        if (row >= totalRows) break;
        for (int c = 0; c < cols; c++) {
            int pi = row * cols + c;
            if (pi >= nPairs) break;
            float x = L.listX + U * 2.5f + c * colW;
            float y = y0 + r * lineH;
            std::string num = std::to_string(pi + 1) + ".";
            text(num, x + numW - textW(num, lts), y, lts, COL_DIM, 0, false);
            for (int k = 0; k < 2; k++) {
                int ply = pi * 2 + k;
                if (ply > lastPly) break;
                float mx = x + numW + U * 1.5f + k * plyW;
                if (ply == lastPly) fillRRect(mx - U * 0.8f, y - U * 0.8f, textW(gM.g.san[ply], lts) + U * 1.6f, textH(lts) + U * 1.6f, U * 0.8f, C(236, 186, 92, 70));
                text(gM.g.san[ply], mx, y, lts, ply == lastPly ? COL_GOLD : COL_TEXT, 0, false);
            }
        }
    }
    if (maxScroll > 0) {
        // полоса прокрутки
        float trackH = rowsVis * lineH;
        float th = std::max(U * 4, trackH * rowsVis / totalRows);
        float tpos = (float)(maxScroll - gListScroll) / maxScroll;
        fillRRect(L.listX + L.listW - U * 1.6f, y0 + (trackH - th) * tpos, U * 0.8f, th, U * 0.4f, C(255, 255, 255, 60));
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
        else if (gConfirm == CF_NEW) { q1 = "НОВАЯ ПАРТИЯ?"; q2 = "ТЕКУЩАЯ ПАРТИЯ НЕ ЗАВЕРШЕНА"; }
        else { q1 = "СБРОСИТЬ?"; q2 = "ВСЯ СТАТИСТИКА БУДЕТ УДАЛЕНА"; }
        int s1 = fitScale(q1, p.w * 0.9f, ts + 2), s2 = fitScale(q2, p.w * 0.9f, ts);
        text(q1, p.x + p.w * 0.5f, p.y + U * 8, s1, COL_GOLD, 1);
        text(q2, p.x + p.w * 0.5f, p.y + U * 8 + textH(s1) + U * 5, s2, COL_DIM, 1, false);
    } else if (gOverlay == OV_RESULT) {
        Panel p = overlayPanel(106);
        drawPanel(p);
        const Game &g = gM.g;
        std::string t1;
        Col tc = COL_GOLD;
        int winner = g.result == RES_WHITE ? eng::WHITE : (g.result == RES_BLACK ? eng::BLACK : -1);
        if (g.result == RES_DRAW) t1 = "НИЧЬЯ";
        else if (gM.mode == MODE_BOT) {
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
        std::string mv = "ХОДОВ: " + std::to_string((g.moves.size() + 1) / 2);
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
    if (gScreen != SC_GAME) ensurePieceTex(std::max(24, (int)(uiU() * 13)));
    switch (gScreen) {
        case SC_MENU: drawMenu(); break;
        case SC_SETUP: drawSetup(); break;
        case SC_STATS: drawStats(); break;
        case SC_GAME: drawGame(); break;
    }
    drawOverlay();
}

// =====================================================================
//                              ВВОД
// =====================================================================
static void goMenu() {
    cancelBot();
    clearSel();
    gOverlay = OV_NONE;
    gResultPending = false;
    gScreen = SC_MENU;
    saveAll();
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
        case B_PLAY_BOT: gSetupMode = MODE_BOT; gScreen = SC_SETUP; break;
        case B_PLAY_TWO: gSetupMode = MODE_TWO; gScreen = SC_SETUP; break;
        case B_STATS: gScreen = SC_STATS; break;
        case B_SOUND: gSoundOn = !gSoundOn; saveAll(); break;
        case B_EXIT: gRunning = false; break;
        case B_LVL1: case B_LVL2: case B_LVL3: case B_LVL4: case B_LVL5: gSet.level = id - B_LVL1 + 1; saveAll(); break;
        case B_COL_W: case B_COL_B: case B_COL_R: gSet.color = id - B_COL_W; saveAll(); break;
        case B_CLK0: case B_CLK1: case B_CLK2: case B_CLK3: gSet.clock = id - B_CLK0; saveAll(); break;
        case B_START: newMatch(gSetupMode, gSet.level, gSetupMode == MODE_BOT ? gSet.color : 0, gSet.clock); break;
        case B_BACK: gScreen = SC_MENU; break;
        case B_UNDO: doUndo(); break;
        case B_RESIGN: gConfirm = CF_RESIGN; gOverlay = OV_CONFIRM; clearSel(); break;
        case B_NEW:
            if (gM.g.result == RES_NONE && !gM.g.moves.empty()) { gConfirm = CF_NEW; gOverlay = OV_CONFIRM; clearSel(); }
            else restartSame();
            break;
        case B_FLIP: gM.flip = !gM.flip; saveAll(); break;
        case B_MENU: goMenu(); break;
        case B_YES: {
            int c = gConfirm;
            gOverlay = OV_NONE;
            gConfirm = CF_NONE;
            if (c == CF_RESIGN) doResign();
            else if (c == CF_NEW) restartSame();
            else if (c == CF_RESET) { gStats = Stats(); saveAll(); }
            break;
        }
        case B_NO: gOverlay = OV_NONE; gConfirm = CF_NONE; break;
        case B_RES_NEW: gOverlay = OV_NONE; restartSame(); break;
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
        default: break;
    }
}

static void onBack() {
    if (gOverlay != OV_NONE) {
        if (gOverlay == OV_PROMO) clearSel();
        gOverlay = OV_NONE;
        gConfirm = CF_NONE;
        return;
    }
    switch (gScreen) {
        case SC_GAME: goMenu(); break;
        case SC_SETUP: case SC_STATS: gScreen = SC_MENU; break;
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
    if (gScreen != SC_GAME) return;
    GameLayout L = gameLayout();
    if (x >= L.listX && x < L.listX + L.listW && y >= L.listY && y < L.listY + L.listH) {
        gPtr.listDrag = true;
        gPtr.listStart = gListScroll;
        return;
    }
    int s = xyToSq(L, x, y);
    if (s < 0) { clearSel(); return; }
    if (!canHumanMove()) return;
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
}

static void pointerMove(float x, float y) {
    gPtr.x = x;
    gPtr.y = y;
    if (!gPtr.down) return;
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
        else if (gOverlay == OV_CONFIRM) { gOverlay = OV_NONE; gConfirm = CF_NONE; }
        return;
    }
    if (gPtr.listDrag) { gPtr.listDrag = false; return; }
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
            if (e.button.which == SDL_TOUCH_MOUSEID || e.button.button != SDL_BUTTON_LEFT) break;
            if (!gPtr.down) {
                gPtr.finger = false;
                pointerDown(e.button.x * gMouseSX, e.button.y * gMouseSY);
            }
            break;
        case SDL_MOUSEMOTION:
            if (e.motion.which == SDL_TOUCH_MOUSEID) break;
            if (!gPtr.finger || !gPtr.down) pointerMove(e.motion.x * gMouseSX, e.motion.y * gMouseSY);
            break;
        case SDL_MOUSEBUTTONUP:
            if (e.button.which == SDL_TOUCH_MOUSEID || e.button.button != SDL_BUTTON_LEFT) break;
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
            gM.tLeft[side] -= dt;
            if (gM.tLeft[side] <= 0) onTimeout(side);
        }
        if (gResultPending && gAnims.empty() && now >= gResultAt) {
            gResultPending = false;
            if (gScreen == SC_GAME && gM.g.result != RES_NONE) gOverlay = OV_RESULT;
        }
    }
    buildScreenButtons();
    buildOverlayButtons();
}

static bool needsAnimation() {
    if (gPtr.down || !gAnims.empty() || botThinking() || gResultPending) return true;
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
        if (SDL_WaitEventTimeout(&e, 500)) {
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
