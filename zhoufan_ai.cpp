#include <ctime>
#include <cstdlib>
#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <queue>

using namespace std;

//#define DEBUG
//#define CHECK_LOSE
//#define SORT_MOVE
#define DIS_VALUE
#define HISTORY

const bool allowSuicide = false;

const int totNum = 25;
const int totKind = 12;
const int upperL = 11, upperR = 16;
const int lowerL = 0, lowerR = 5;
const int H = 17;
const int W = 5;

const int INF0 = 999999999, INF1 = 99999999, INF2 = 77777777, winScore = 88888888, winConst = 99999999;

// 0,  1,  2,  3,  4,  5,  6,  7
// D,  L,  U,  R, UL, UR, DR, DL
const int dx[8] = {-1, 0, 1, 0, 1, 1, -1, -1};
const int dy[8] = {0, -1, 0, 1, -1, 1, 1, -1};
const int invDir[8] = {2, 3, 0, 1, 6, 7, 4, 5};

const double clocksPerMS = (double)CLOCKS_PER_SEC / 1000.0;
const double timeLimit = 990.0;

clock_t startT, endT, durT;

const int limDepth = 10;

int id, cntStep, finalDepth, cntNode, fy0, fy1;
int map[H][W], A[H][W], validDir[H][W][8], railDir[H][W][8];

bool timeOutWarning;

//Normal-0 HeadQuarter-1 Camp-2 RailwayStation-3
int mark[H][W] = {
                    {0, 1, 0, 1, 0},
                    {3, 3, 3, 3, 3},
                    {3, 2, 0, 2, 3},
                    {3, 0, 2, 0, 3},
                    {3, 2, 0, 2, 3},
                    {3, 3, 3, 3, 3},
                    {3, 0, 3, 0, 3},
                    {0, 0, 0, 0, 0},
                    {3, 0, 3, 0, 3},
                    {0, 0, 0, 0, 0},
                    {3, 0, 3, 0, 3},
                    {3, 3, 3, 3, 3},
                    {3, 2, 0, 2, 3},
                    {3, 0, 2, 0, 3},
                    {3, 2, 0, 2, 3},
                    {3, 3, 3, 3, 3},
                    {0, 1, 0, 1, 0},
                 };

//Normal-0 Flag-1 NearFlag-2 CampOverFlag-3 PosOverMineFlag-4
int smark[H][W];

//司令-0 军长-1 师长-2 旅长-3 团长-4 营长-5 连长-6 排长-7 工兵-8 地雷-9 炸弹-10 军棋-11
const int valRank[totKind] = {5120, 2560, 1280, 640, 320, 160, 80, 40, 0};
const int valBomb = 2000, valMine = 1200, val8Base = 1600, val8Second = 1000, valSmark3 = 300, valCamp = 0, valOpen = 7000;

bool Exist(int x, int y) {
    return (lowerL <= x && x <= lowerR && 0 <= y && y < W)
		|| (upperL <= x && x <= upperR && 0 <= y && y < W)
		|| ((x == 6 || x == 8 || x == 10) && (y == 0 || y == 2 || y == 4));
}

void Initialize() {
    cntStep = 0;

    //set map[][] = -1
    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            map[i][j] = -1;
        }
    }

    //set validDir[][][] and railDir[][][]
    // 0,  1,  2,  3,  4,  5,  6,  7
    // D,  L,  U,  R, UL, UR, DR, DL
    memset(validDir, 0, sizeof(validDir));
    memset(railDir, 0, sizeof(railDir));
    int xx, yy, t;
    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            if (!Exist(i, j)) continue;

            //Dir-[0, 3]
            if (i > lowerR && i < upperL) {
                if (i == 6) {
                    validDir[i][j][0] = 1;
                    validDir[i][j][2] = 2;
                }
                if (i == 8) {
                    validDir[i][j][0] = 2;
                    validDir[i][j][2] = 2;
                }
                if (i == 10) {
                    validDir[i][j][0] = 2;
                    validDir[i][j][2] = 1;
                }
                if (j == 0) {
                    validDir[i][j][3] = 2;
                }
                if (j == 2) {
                    validDir[i][j][1] = 2;
                    validDir[i][j][3] = 2;
                }
                if (j == 4) {
                    validDir[i][j][1] = 2;
                }
            }
            else {
                for (int k = 0; k < 4; ++k) {
                    xx = i + dx[k]; yy = j + dy[k];
                    if (Exist(xx, yy)) {
                        validDir[i][j][k] = 1;
                    }
                }
            }
            for (int k = 0; k < 4; ++k) {
                //mark: RailwayStation-3
                if ((mark[i][j] != 3) || (!validDir[i][j][k])) continue;
                t = validDir[i][j][k];
                xx = i + t * dx[k]; yy = j + t * dy[k];
                if (mark[xx][yy] == 3) {
                    railDir[i][j][k] = validDir[i][j][k];
                }
            }

            //Dir-[4, 7]
            //mark: Camp-2
            if (mark[i][j] == 2) {
                for (int k = 4; k < 8; ++k) {
                    validDir[i][j][k] = 1;
                    xx = i + dx[k]; yy = j + dy[k];
                    validDir[xx][yy][invDir[k]] = 1;
                }
            }
        }
    }

    #ifdef DEBUG
        for (int i = 0; i < 4; ++i)
            cerr << validDir[16][2][i] << " ";
        cerr << endl;
    #endif // DEBUG
}

//Normal-0 Flag-1 NearFlag-2 CampOverFlag-3 PosOverMineFlag-4
void AnalyseInit() {
    memset(smark, 0, sizeof(smark));
    //Flag0-11 Flag1-23
    for (int i = 1; i <= 3; i += 2) {
        if (map[0][i] == 11) {
            fy0 = i;
            smark[0][i] = 1;
            smark[0][i - 1] = smark[0][i + 1] = 2;
            smark[2][i] = 3;
            smark[1][i] = 4;
        }
        if (map[16][i] == 23) {
            fy1 = i;
            smark[16][i] = 1;
            smark[16][i - 1] = smark[16][i + 1] = 2;
            smark[14][i] = 3;
            smark[15][i] = 4;
        }
    }

    //Mine0-9 Mine1-21
    for (int i = 0; i <= 4; i += 2) {
        if (map[0][i] == 9) {
            smark[1][i] = 4;
        }
        if (map[16][i] == 21) {
            smark[15][i] = 4;
        }
    }
}

inline int Abs(int x) {
    return x < 0 ? -x : x;
}

int Distance(int x, int y, int xx, int yy) {
    return Abs(x - xx) + Abs(y - yy);
}

int numKind[2][totKind], rankKind[totKind], valKind[2][totKind];

//司令-0 军长-1 师长-2 旅长-3 团长-4 营长-5 连长-6 排长-7 工兵-8 地雷-9 炸弹-10 军棋-11
int CalcScore() {
    int ret, score[2] = {0, 0};
    int col, kind;
    bool open[2];

    //get valKind[] && open[]
    int cntMine[2] = {0, 0};
    //Mine0-9 Mine1-21
    if (A[0][fy0 - 1] == 9 || A[1][fy0 - 1] == 9) ++cntMine[0];
    if (A[1][fy0] == 9) ++cntMine[0];
    if (A[0][fy0 + 1] == 9 || A[1][fy0 + 1] == 9) ++cntMine[0];
    if (A[16][fy1 - 1] == 21 || A[15][fy1 - 1] == 21) ++cntMine[1];
    if (A[15][fy1] == 21) ++cntMine[1];
    if (A[16][fy1 + 1] == 21 || A[15][fy1 + 1] == 21) ++cntMine[1];
    for (int i = 0; i <= 1; ++i) {
        open[i] = (cntMine[i] < 3);
    }
    for (int i = 0; i < totKind; ++i) {
        numKind[0][i] = numKind[1][i] = 0;
    }
    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            //A[i][j] == -1 when !Exist(i, j)
            if (A[i][j] == -1) continue;
            col = A[i][j] / totKind;
            kind = A[i][j] % totKind;
            ++numKind[col][kind];
        }
    }
    int nowRank = 0;
    for (int i = 0; i <= 7; ++i) {
        if (numKind[0][i] + numKind[1][i] == 0) continue;
        rankKind[i] = nowRank++;
        valKind[0][i] = valKind[1][i] = valRank[rankKind[i]];
    }
    for (int i = 0; i <= 1; ++i) {
        if (!open[i ^ 1]) {
            valKind[i][8] = val8Base;
            valKind[i][8] += 80 * (3 - numKind[i][8]);
        }
        else {
            valKind[i][8] = max(valRank[nowRank], val8Second);
            valKind[i][8] += 60 * (3 - numKind[i][8]);
        }
        valKind[i][9] = valMine;
        valKind[i][10] = valBomb;
        valKind[i][11] = INF1;
    }

    //calculate score
    for (int i = 0; i <= 1; ++i) {
        if (open[i ^ 1]) {
            score[i] += valOpen;
        }
    }
    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            if (A[i][j] == -1) continue;
            col = A[i][j] / totKind;
            kind = A[i][j] % totKind;
            score[col] += valKind[col][kind];
        #ifdef DIS_VALUE
            if (col == 0) {
                score[0] += Distance(i, j, 16, fy1);
            }
            else {
                score[1] += Distance(i, j, 0, fy0);
            }
        #endif // DIS_VALUE
            if ((col == 0 && i >= upperL) || (col == 1 && i <= lowerR)) {
                if (smark[i][j] == 2) score[col] += INF2;
                if (smark[i][j] == 3) score[col] += valSmark3;
                if (mark[i][j] == 2) score[col] += valCamp;
            }
        }
    }

    if (id == 0) ret = score[0] - score[1];
    else ret = score[1] - score[0];
    return ret;
}

const int maxRailHis = 45;

struct Point {
    int x, y;

    Point() {}
    Point(int a, int b) {
        x = a; y = b;
    }
} history[maxRailHis];

int hisTop;

queue<Point> Q;

bool visited[H][W];

int scoreMove[H][W][H][W];

struct Move {
    int x, y, xx, yy, ft, idx;

    Move() {}
    Move(int a, int b, int c, int d, int e) {
        x = a; y = b; xx = c; yy = d; ft = e;
    }
} ans;

const int maxMove = 150;
int valMove[maxMove];

bool CmpV(Move m1, Move m2) {
    return valMove[m1.idx] > valMove[m2.idx];
}

bool CmpH(Move m1, Move m2) {
    return scoreMove[m1.x][m1.y][m1.xx][m1.yy] > scoreMove[m2.x][m2.y][m2.xx][m2.yy];
}

//1:k-win 0:all-die -1:k1-win
int CmpKind(int k, int k1) {
    if (k == 10 || k1 == 10) return 0;
    if (k1 == 11) return 1;
    if (k1 == 9) {
        if (k == 8) return 1;
        return -1;
    }
    if (k < k1) return 1;
    if (k == k1) return 0;
    if (k > k1) return -1;
}

bool CanAdd(int x, int y, int xx, int yy, int col, int kind, int &ft) {
    //HeadQuarter which is not Flag
    if (mark[xx][yy] == 1 && smark[xx][yy] != 1) {
        return false;
    }
    if (A[xx][yy] == -1) {
        ft = A[x][y];
        return true;
    }
    //Nonempty Camp
    if (mark[xx][yy] == 2) {
        return false;
    }
    int col1, kind1, cmp;
    col1 = A[xx][yy] / totKind;
    kind1 = A[xx][yy] % totKind;
    if (col1 == col) {
        return false;
    }
    cmp = CmpKind(kind, kind1);
    if (cmp > 0) {
        ft = A[x][y];
        return true;
    }
    if (cmp == 0) {
        ft = -1;
        return true;
    }
    if (cmp < 0) {
        if (!allowSuicide) return false;
        ft = A[xx][yy];
        return true;
    }
}

inline int Sqr(int x) {
    return x * x;
}

int worstScore, bestScore;

int DFS(int depth, int nowCol, int alpha, int beta) {
    //check if TimeOut Warning
    endT = clock();
    durT = endT - startT;
    if ((double)durT / clocksPerMS > timeLimit) {
        timeOutWarning = true;
        return -INF0;
    }

    //return when then opponent wins
    if (A[0][fy0] != 11) {
        if (id == 0) return -winConst;
        else return winConst;
    }
    if (A[16][fy1] != 23) {
        if (id == 1) return -winConst;
        else return winConst;
    }

    //Final Depth Return
    if (depth == finalDepth) {
        ++cntNode;
        return CalcScore();
    }

    //Generate Moves
    int topMove = 0;
    Move moveSet[maxMove];
    int col, kind, col1, kind1;
    int x, y, xx, yy, t, ft, cmp;
    memset(visited, 0, sizeof(visited));
    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            if (A[i][j] == -1) continue;
            //HeadQuarter-1
            if (mark[i][j] == 1) continue;
            col = A[i][j] / totKind;
            if (col != nowCol) continue;
            kind = A[i][j] % totKind;
            if (kind == 9 || kind == 11) continue;
            if (kind == 8 && mark[i][j] == 3) {
                while (!Q.empty()) Q.pop();
                Point s, now;
                hisTop = 0;
                s = Point(i, j);
                visited[i][j] = true;
                Q.push(s);
                history[++hisTop] = s;
                while (!Q.empty()) {
                    now = Q.front(); Q.pop();
                    for (int k = 0; k < 4; ++k) {
                        if (!railDir[now.x][now.y][k]) continue;
                        t = railDir[now.x][now.y][k];
                        xx = now.x + t * dx[k];
                        yy = now.y + t * dy[k];
                        if (visited[xx][yy]) continue;
                        visited[xx][yy] = true;
                        history[++hisTop] = Point(xx, yy);
                        if (A[xx][yy] == -1) {
                            Q.push(Point(xx, yy));
                            if (smark[xx][yy] == 4 && xx / 9 == col ^ 1) {
                                if (CanAdd(i, j, xx, yy, col, kind, ft)) {
                                    moveSet[++topMove] = Move(i, j, xx, yy, ft);
                                }
                            }
                        }
                        else {
                            if (CanAdd(i, j, xx, yy, col, kind, ft)) {
                                moveSet[++topMove] = Move(i, j, xx, yy, ft);
                            }
                        }
                    }
                }
                while (hisTop) {
                    now = history[hisTop--];
                    visited[now.x][now.y] = false;
                }
            }
            for (int k = 0; k < 8; ++k) {
                if (!validDir[i][j][k]) continue;
                if (k < 4 && railDir[i][j][k]) {
                    if (kind == 8) continue;
                    xx = i; yy = j;
                    while (true) {
                        t = railDir[xx][yy][k];
                        xx += t * dx[k]; yy += t * dy[k];
                        if (CanAdd(i, j, xx, yy, col, kind, ft)) {
                            moveSet[++topMove] = Move(i, j, xx, yy, ft);
                        }
                        if (!railDir[xx][yy][k] || A[xx][yy] != -1) break;
                    }
                }
                else {
                    xx = i + dx[k]; yy = j + dy[k];
                    if (CanAdd(i, j, xx, yy, col, kind, ft)) {
                        moveSet[++topMove] = Move(i, j, xx, yy, ft);
                    }
                }
            }
        }
    }

#ifdef SORT_MOVE
    //Sort Moves at depth-0
    if (depth == 0) {
        for (int i = 1; i <= topMove; ++i) {
            moveSet[i].idx = i;
        }
        sort(moveSet + 1, moveSet + topMove + 1, CmpV);
    }
#endif // SORT_MOVE

#ifdef HISTORY
    sort(moveSet + 1, moveSet + topMove + 1, CmpH);
#endif // HISTORY

    //Get bestScore
    int bestScore, nowScore, cntBestMove = 0;
    Move bestMove[maxMove];
    if (nowCol != id) bestScore = INF0;
    else bestScore = -INF0;
    int oriAt, oriAtt;
    for (int i = 1; i <= topMove; ++i) {
        x = moveSet[i].x; y = moveSet[i].y;
        xx = moveSet[i].xx; yy = moveSet[i].yy;
        oriAt = A[x][y]; oriAtt = A[xx][yy];
        A[x][y] = -1; A[xx][yy] = moveSet[i].ft;
        nowScore = DFS(depth + 1, nowCol ^ 1, alpha, beta);
        if (depth == 0) {
            valMove[moveSet[i].idx] = nowScore;
        #ifdef CHECK_LOSE
            worstScore = min(worstScore, nowScore);
        #endif // CHECK_LOSE
        }
    #ifdef DEBUG
        if (depth == 0) {
            cerr << "MOVE: (" << x << ", " << y << ") to (" << xx << ", " << yy << ") with " << nowScore << endl;
        }
    #endif // DEBUG
        A[x][y] = oriAt; A[xx][yy] = oriAtt;
        if (timeOutWarning) break;
        if (nowScore == bestScore) {
            bestMove[cntBestMove++] = moveSet[i];
        }
        if (nowCol != id) {
            if (nowScore < bestScore) {
                bestScore = nowScore;
                cntBestMove = 1;
                bestMove[0] = moveSet[i];
                beta = nowScore;
            }
        }
        else {
            if (nowScore > bestScore) {
                bestScore = nowScore;
                cntBestMove = 1;
                bestMove[0] = moveSet[i];
                alpha = nowScore;
            }
        }
        if (alpha >= beta) {
            scoreMove[x][y][xx][yy] += Sqr(finalDepth - depth + 1);
            if (nowCol != id) return -INF0;
            else return INF0;
        }
    }

    if (timeOutWarning) return -INF0;
    for (int i = 0; i < cntBestMove; ++i) {
        scoreMove[bestMove[i].x][bestMove[i].y][bestMove[i].xx][bestMove[i].yy] += Sqr(finalDepth - depth + 1);
    }
    if (depth == 0) {
        ans = bestMove[rand() % cntBestMove];
    }
    return bestScore;
}

void MakeDecision(int &ax, int &ay, int &axx, int &ayy) {
#ifdef HISTORY
    memset(scoreMove, 0, sizeof(scoreMove));
#endif // HISTORY

    for (int i = 0; i < H; ++i) {
        for (int j = 0; j < W; ++j) {
            A[i][j] = map[i][j];
        }
    }
#ifdef DEBUG
    for (int i = H-1; i >= 0; --i) {
        for (int j = 0; j < W; ++j) {
            cerr << A[i][j] << " ";
        }
        cerr << endl;
    }
#endif // DEBUG
    memset(valMove, 0, sizeof(valMove));
    for (int d = 1; d <= limDepth; ++d) {
        finalDepth = d;
        cntNode = 0;
        bestScore = DFS(0, id, -INF0, INF0);
        cerr << "Depth: " << d << ", cntNode: " << cntNode << endl;
        if (bestScore > winScore) {
            cerr << "I have a strong feeling of the Force." << endl;
            break;
        }
    #ifdef CHECK_LOSE
        if (worstScore < -winScore) {
            cerr << "I have a bad feeling about this." << endl;
            break;
        }
    #endif // CHECK_LOSE
        if (timeOutWarning) {
            cerr << "TimeOut Warning" << endl;
            break;
        }
    }
    ax = ans.x; ay = ans.y;
    axx = ans.xx; ayy = ans.yy;
    cerr << endl;
}

/***************************************************** The Force ***********************************************************/

void Change() {
    int x, y, xx, yy, col, kind;
    cin >> x >> y >> xx >> yy >> col >> kind;
    if (kind == -2) kind = -1;
    ++cntStep;
	cerr << "Get updates for step " << cntStep << ": "  << endl;
	cerr << "AI-" << col << " (" << x << ", " << y << ") to (" << xx << ", " << yy << ") restKind-" << kind << "\n" << endl;
    int tar = col * totKind + kind;
    if (x == xx && y == yy) map[x][y] = tar;
    else {
        map[x][y] = -1;
        map[xx][yy] = tar;
    }
}

//司令-0 军长-1 师长-2 旅长-3 团长-4 营长-5 连长-6 排长-7 工兵-8 地雷-9 炸弹-10 军棋-11
void ShowInit(int id) {
    /*cout << "9 11 9 7 7 6 9 6 8 8 8 6 5 5 4 7 10 1 10 0 3 2 2 4 3" << endl;
	cerr << "Arrangement: 9 11 9 7 7 6 9 6 8 8 8 6 5 5 4 7 10 1 10 0 3 2 2 4 3" << endl;*/
    cout << "9 11 9 7 6 6 9 7 4 3 2 5 8 10 5 8 4 1 6 10 3 8 0 7 2" << endl;
	cerr << "Arrangement: 9 11 9 7 6 6 9 7 4 3 2 5 8 10 5 8 4 1 6 10 3 8 0 7 2" << endl;
}

void GetInit() {
	int arr0[25], arr1[25];
	for (int i = 0; i < 25; ++i) {
		cin >> arr0[i];
	}
	for (int i = 0; i < 25; ++i) {
		cin >> arr1[i];
		arr1[i] += totKind;
	}
	map[0][0] = arr0[0];
	map[0][1] = arr0[1];
	map[0][2] = arr0[2];
	map[0][3] = arr0[3];
	map[0][4] = arr0[4];
	map[1][0] = arr0[5];
	map[1][1] = arr0[6];
	map[1][2] = arr0[7];
	map[1][3] = arr0[8];
	map[1][4] = arr0[9];
	map[2][0] = arr0[10];
	map[2][2] = arr0[11];
	map[2][4] = arr0[12];
	map[3][0] = arr0[13];
	map[3][1] = arr0[14];
	map[3][3] = arr0[15];
	map[3][4] = arr0[16];
	map[4][0] = arr0[17];
	map[4][2] = arr0[18];
	map[4][4] = arr0[19];
	map[5][0] = arr0[20];
	map[5][1] = arr0[21];
	map[5][2] = arr0[22];
	map[5][3] = arr0[23];
	map[5][4] = arr0[24];

	map[16][0] = arr1[4];
	map[16][1] = arr1[3];
	map[16][2] = arr1[2];
	map[16][3] = arr1[1];
	map[16][4] = arr1[0];
	map[15][0] = arr1[9];
	map[15][1] = arr1[8];
	map[15][2] = arr1[7];
	map[15][3] = arr1[6];
	map[15][4] = arr1[5];
	map[14][0] = arr1[12];
	map[14][2] = arr1[11];
	map[14][4] = arr1[10];
	map[13][0] = arr1[16];
	map[13][1] = arr1[15];
	map[13][3] = arr1[14];
	map[13][4] = arr1[13];
	map[12][0] = arr1[19];
	map[12][2] = arr1[18];
	map[12][4] = arr1[17];
	map[11][0] = arr1[24];
	map[11][1] = arr1[23];
	map[11][2] = arr1[22];
	map[11][3] = arr1[21];
	map[11][4] = arr1[20];
}

inline void End() {
    std::cout << "END\n" << std::flush;
}

int main(int argc, char **argv) {
    unsigned seed = time(0);
    if (argc == 2) {
        cerr << "Skywalker gets given seed = " << argv[1] << endl;
        seed = 0;
        for (char *pc = argv[1]; *pc; ++pc)
            seed = seed * 10 + (*pc - '0');
    }
    srand(seed);

    Initialize();

    string op;
    while (true) {
        cin >> op;
        if (op == "id") {
            cin >> id;
			cerr << "$ fanzhou, ID: " << id << "\n" << endl;
            cout << "fanzhou" << endl;
            End();
		} else if (op == "refresh") {
            GetInit();
            AnalyseInit();
            cerr << "#GetInit\n" << endl;
        } else if (op == "init") {
			ShowInit(id);
            cerr << "#ShowInit\n" << endl;
			End();
		} else if (op == "message") {
            Change();
        } else if (op == "action") {
            startT = clock();
            timeOutWarning = false;
            int ax, ay, axx, ayy;
            MakeDecision(ax, ay, axx, ayy);
			cout << ax << " " << ay << " " << axx << " " << ayy << endl;
            cerr << "Action: (" << ax << ", " << ay << ") to (" << axx << ", " << ayy << ")\n" << endl;
            End();
        }
    }
}
