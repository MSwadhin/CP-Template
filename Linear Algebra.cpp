/**
------ Kirchhof's Thm
To count the number of spanning trees in an undirected graph G
create an N*N matrix mat, and for each edge (a,b) in G, do
mat[a][a]++, mat[b][b]++, mat[a][b]--, mat[b][a]--.
Remove the last row and column, and take the determinant.
*/
const int mod = 1e9+7;
inline LL inv(LL n) {return powerMod(n,mod-2,mod);}
inline LL Mul(LL a,LL b) {return (a*b)%mod;}
inline LL Div(LL a,LL b) {return Mul(a,inv(b));}
const int maxn = 35;
namespace MujahidMatrix{
    class Matrix{
    public:
        int row,col;
        LL M[maxn][maxn];
        Matrix( int a=maxn,int b=maxn ){
            row = a,col = b;
            for(int i=0;i<row;i++)
                for(int j=0;j<col;j++)
                    M[i][j] = 0;
        }
    };
    Matrix matrixMul( const Matrix &a,const Matrix &b ){
        Matrix m = Matrix(a.row,b.col);
        for(int k=0;k<a.row;k++)
            for(int i=0;i<a.col;i++)
                for(int j=0;j<b.col;j++)
                    m.M[k][j] = ( m.M[k][j]%mod + ( 1LL * a.M[k][i]%mod *b.M[i][j]%mod ) % mod )%mod;
        return m;
    }
    Matrix bigModMat( Matrix m,LL p ){
        if( p==1 )return m;
        Matrix cur = bigModMat( m,p/2 );
        cur = matrixMul( cur,cur );
        if( p%2 )
            cur = matrixMul( cur,m );
        return cur;
    }

    LL Det(Matrix mat){ // N^3
        assert(mat.row == mat.col);
        int n = mat.row;
        LL ret = 1;
        for(int i = 1; i <= n; i++){
            for(int j = i + 1; j <= n; j++){
                while(mat.M[j][i]){
                    LL t = Div(mat.M[i][i], mat.M[j][i]);
                    for(int k = i; k <= n; ++k){
                        mat.M[i][k] -= Mul(mat.M[j][k] , t);
                        if(mat.M[i][k] < 0) mat.M[i][k] += mod;
                        swap(mat.M[j][k], mat.M[i][k]);
                    }
                    ret = mod - ret;
                }
            }
            if(mat.M[i][i] == 0) return 0;
            ret = Mul(ret, mat.M[i][i]);
        }
        if(ret < 0) ret += mod;
        return ret;
    }

    LL Tmp[maxn<<1][maxn<<1];
    Matrix Inverse(Matrix mat){ //N^3
        assert(mat.row == mat.col);
        assert(Det(mat) != 0);
        int n = mat.row;
        //mat.normalize();%=mod for all value
        for(int i=1;i<=n;i++){
            for(int j=1;j<=n;j++) Tmp[i][j] = mat.M[i][j];
            for(int j=n+1; j<=2*n; j++) Tmp[i][j] = 0;
            Tmp[i][i+n] = 1;
        }
        for(int i=1; i<=n; i++){
            assert(Tmp[i][i] != 0);
            for(int j=1; j<=n; j++){
                if(i == j) continue;
                LL c = Div(Tmp[j][i], Tmp[i][i]);
                for(int k=i; k<=2*n; k++){
                    Tmp[j][k] = Tmp[j][k] - Mul(Tmp[i][k], c);
                    if(Tmp[j][k] < 0) Tmp[j][k] += mod;
                }
            }
        }
        Matrix Inv(n,n);
        for(int i=1; i<=n; i++){
            for(int j = 1; j <= n; j++){
                Inv.M[i][j] = Div(Tmp[i][j+n], Tmp[i][i]);
            }
        }
        return Inv;
    }

    //Freivalds algorithm : check whether AB = C
    //Complexity : O(iteration * n^2)
    int p[maxn],q[maxn],r[maxn];
    bool Freivalds(Matrix A,Matrix B,Matrix C){
        srand(time(NULL));
        int n=A.row;
        int iteration=15;
        int Yes=0;
        for(int it=1;it<=iteration;it++){
            for(int i=1;i<=n;i++) r[i] = rand()%2;
            for(int i=1;i<=n;i++) p[i] = q[i] = 0;
            for(int i=1;i<=n;i++) for(int j=1;j<=n;j++)
                    p[i] += r[j] * A.M[i][j];
            for(int i=1;i<=n;i++) for(int j=1;j<=n;j++)
                    q[i] += p[j] * B.M[i][j];
            for(int i=1;i<=n;i++) for(int j=1;j<=n;j++)
                    q[i] -= r[j] * C.M[i][j];
            bool All = true;
            for(int i=1;i<=n;i++) if(q[i]) All=false;
            if(All) Yes++;
        }
        return Yes == iteration;
    }
}
/***
Gauss-Jordan Elimination
n = number of linear equations
m = number of variables
ar[i][m] = right-hand side value of constants
2x + y -z = 8      ----->  (i)
-3x -y + 2z = -11  ----->  (ii)
-2x + y + 2z = -3  ----->  (iii)
n = 3 (x, y, z), m = 3 (i, ii, iii)
ar[0] = {2, 1, -1, 8}    ----->  (i)
ar[1] = {-3, -1, 2, -11} ----->  (ii)
ar[2] = {-2, 1, 2, -3}   ----->  (iii)
Returns -1 when there is no solution
Otherwise returns the number of independent variables (0 for an unique solution)
Contains a solution in the vector res on successful completion
Note that the array is modified in the process
Notes:
For solving problems on graphs with probability/expectation, make sure the graph
is connected and a single component. If not, then re-number the vertex and solve
for each connected component separately.
***/
// N^3
int gauss(int n, int m, double ar[102][102], vector<double>& res){
    res.assign(m, 0);
    vector <int> pos(m, -1);
    const double EPS = 1e-9;
    int i, j, k, l, p, free_var = 0;
    for (j = 0, i = 0; j < m && i < n; j++){
        for (k = i, p = i; k < n; k++)if (fabs(ar[k][j]) > fabs(ar[p][j])) p = k;
        if (fabs(ar[p][j]) > EPS){
            pos[j] = i;
            for (l = j; l <= m; l++) swap(ar[p][l], ar[i][l]);
            for (k = 0; k < n; k++){
                if (k != i){
                    double x = ar[k][j] / ar[i][j];
                    for (l = j; l <= m; l++) ar[k][l] -= (ar[i][l] * x);
                }
            }
            i++;
        }
    }
    for (i = 0; i < m; i++){
        if (pos[i] == -1) free_var++;
        else res[i] = ar[pos[i]][m] / ar[pos[i]][i];
    }
    for (i = 0; i < n; i++) {
        double val = 0.0;
        for (j = 0; j < m; j++) val += (res[j] * ar[i][j]);
        if (fabs(val - ar[i][m]) > EPS) return -1;
    }
    return free_var;
}
/// Gaussian elimination in field MOD (MOD should be a prime) N^3 * log(MOD)
int gauss(int n, int m, int MOD, int ar[102][103], vector<int>& res){
    res.assign(m, 0);
    vector <int> pos(m, -1);
    int i, j, k, l, p, d, free_var = 0;
    const long long MODSQ = (long long)MOD * MOD;
    for (j = 0, i = 0; j < m && i < n; j++){
        for (k = i, p = i; k < n; k++){
            if (ar[k][j] > ar[p][j]) p = k;
        }
        if (ar[p][j]){
            pos[j] = i;
            for (l = j; l <= m; l++) swap(ar[p][l], ar[i][l]);
            d = powerMod(ar[i][j], MOD - 2, MOD);
            for (k = 0; k < n && d; k++){
                if (k != i && ar[k][j]){
                    int x = ((long long)ar[k][j] * d) % MOD;
                    for (l = j; l <= m && x; l++){
                        if (ar[i][l]) ar[k][l] = (MODSQ + ar[k][l] - ((long long)ar[i][l] * x)) % MOD;
                    }
                }
            }
            i++;
        }
    }
    for (i = 0; i < m; i++){
        if (pos[i] == -1) free_var++;
        else res[i] = ((long long)ar[pos[i]][m] * powerMod(ar[pos[i]][i], MOD - 2, MOD)) % MOD;
    }
    for (i = 0; i < n; i++) {
        long long val = 0;
        for (j = 0; j < m; j++) val = (val + ((long long)res[j] * ar[i][j])) % MOD;
        if (val != ar[i][m]) return -1;
    }
    return free_var;
}
/***
Gauss-Jordan Elimination in Galois Field, GF(2), (N^3)/32
*/
#define MAXROW 111
#define MAXCOL 111
int gauss(int n, int m, bitset <MAXCOL> ar[MAXROW], bitset <MAXCOL>& res){
    res.reset();
    vector <int> pos(m, -1);
    int i, j, k, l, v, p, free_var = 0;
    for (j = 0, i = 0; j < m && i < n; j++){
        for (k = i, p = i; k < n; k++){
            if (ar[k][j]){
                p = k;
                break;
            }
        }
        if (ar[p][j]){
            pos[j] = i;
            swap(ar[p], ar[i]);
            for (k = 0; k < n; k++){
                if (k != i && ar[k][j]) ar[k] ^= ar[i];
            }
            i++;
        }
    }
    for (i = 0; i < m; i++){
        if (pos[i] == -1) free_var++;
        else res[i] = ar[pos[i]][m];
    }
    for (i = 0; i < n; i++) {
        for (j = 0, v = 0; j < m; j++) v ^= (res[j] & ar[i][j]);
        if (v != ar[i][m]) return -1;
    }
    return free_var;
}

/*
* Vector Basis
*/
const int d=64;// d-> number of bits
LL basis[d]; // basis[i] keeps the mask of the vector whose f value is i
int sz; // Current size of the basis
void insertVector(LL mask) {
	for (int i = d-1; i>=0 ; i--) {
		if ((mask & (1LL << i)) == 0) continue; // continue if i != f(mask)
		if (!basis[i]) { // If there is no basis vector with the i'th bit set, then insert this vector into the basis
			basis[i] = mask;
			++sz;
			return;
		}
		mask ^= basis[i]; // Otherwise subtract the basis vector from this vector
	}
}
LL maxsubsetxor(){
    LL ans = 0;
    for(int i=d-1;i>=0;i--){
        if(!basis[i])continue;
        if(ans&(1LL<<i))continue;
        ans ^= basis[i];
    }
    return ans;
}
//returns k-th (0-indexed) smallest "distinct" subset xor
LL getKth(LL k){
    LL ans = 0;
    for(LL i = 0; i < d; i++)
        if( basis[i] && ((k>>1)&1) )ans ^= basis[i];
    return ans;
}
int query(int k) { // kth smallest subset xor
	int mask = 0;
	int tot = 1 << sz;
	for (int i = LOG_K - 1; i >= 0; i--)
		if (basis[i]) {
			int low = tot / 2;
			if ((low < k && (mask & 1 << i) == 0) ||
				(low >= k && (mask & 1 << i) > 0)) mask ^= basis[i];
			if (low < k) k -= low;
			tot /= 2;
		}
	return mask;
}
//Thomas algorithm to solve tri-digonal system of equations in O(n)
//Trigonal Eqn : A[i]*X[i-1] + B[i]*X[i] + C[i]*X[i+1] = D[i] [1...n]
// Usually A[1]=C[n]=0
#define LD long double
struct equation{
    LD a, b, c, d;
    equation(){}
    equation(LD a, LD b, LD c, LD d=0.0):
        a(a), b(b), c(c), d(d){}
};
vector<LD> thomas_algorithm(int n,vector<struct equation>ar){
    ar[0].c = ar[0].c / ar[0].b;
    ar[0].d = ar[0].d / ar[0].b;
    for (int i = 1; i < n; i++){
        LD v = 1.0 / (ar[i].b - ar[i].a * ar[i - 1].c);
        ar[i].c = ar[i].c * v;
        ar[i].d = (ar[i].d - ar[i].a * ar[i - 1].d) * v;
    }
    for (int i=n-2;i>=0;i--) ar[i].d = ar[i].d - ar[i].c * ar[i + 1].d;
    vector <LD> res;
    for (int i = 0; i < n; i++) res.push_back(ar[i].d);
    return res;
}