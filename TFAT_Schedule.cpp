#include<iostream>
#include<cstdio>
#include<ctime>
#include<cmath>
#include<cstdlib>
#include<vector>
#include<map>
#include<cstring>
#define maxn 500
#define L 2000
#define minD 1000
#define maxD 400
#define maxD2 400
#define beta 6
#define gamma 0.6
#define inf 0x3f3f3f3f
using namespace std;



const int N = 109, BS_num = 9, K = 3;
double X[maxn], Y[maxn];
double T[maxn][maxn], T1[maxn][maxn], dis[maxn][maxn], h[maxn][maxn];

int exist_s[maxn], exist_r[maxn], skip_s[maxn], skip_r[maxn];
double rest[maxn][maxn];
double best_so_far = inf;
double sumI[maxn];
double mst;
double C[maxn];
int rd = 0, query = 0;

struct Node{
	int w, u, v, num;
	double x;
	vector<Node*> ch;
	Node *f;	
	int sw, su, sv, r;
	Node(int _w, int _u, int _v, int _r) :
		w(_w), u(_u), v(_v), num(0), x(0), r(_r), f(NULL), sw(-1), su(-1), sv(-1){}
};
int vis[maxn];
int f[maxn];

const double p = 0.2, noise = 1e-11, B = 10;
int budget;
double accumulation = 0;
double expired, disconnect, dcnt;

double normal() {
    double u1 = (double)rand() / RAND_MAX; // Uniform(0,1) random number
    double u2 = (double)rand() / RAND_MAX; // Uniform(0,1) random number

    // Box-Muller transform
    double z0 = sqrt(-2.0 * log(u1)) * cos(2.0 * M_PI * u2);
    // double z1 = sqrt(-2.0 * log(u1)) * sin(2.0 * M_PI * u2); // Second independent value

    return z0; // Standard normal random number
}


double rayleigh(){
	double x = normal();
	double y = normal();
	return sqrt(x*x + y*y);
} 

const int MM = 1;
int M;
void init(){
	M = MM;
	for(int i = 0; i < N-BS_num; i++){
		X[i] = rand()/double(RAND_MAX)*L;
		Y[i] = rand()/double(RAND_MAX)*L;	
	}
	
	for(int i = N-BS_num; i < N; i++){
		X[i] = 200 + (i-(N-BS_num))/K * 800;
		Y[i] = 200 + (i-(N-BS_num))%K * 800;
	}
	for(int i = 0; i < N; i++){
		for(int j = 0; j < N; j++){
			h[i][j] = rayleigh();
			dis[i][j] = sqrt((X[i]-X[j])*(X[i]-X[j]) + (Y[i]-Y[j])*(Y[i]-Y[j]));
			if(j < N-BS_num)
				T[i][j] = M/(B*log(1+p/noise/pow(dis[i][j], 4)));
		}	
	}
	for(int i = 0; i < N; i++) dis[i][N] = dis[N][i] = inf;
	vis[N] = 1;
}

void dynamic(double t){
	for(int i = 0; i < N-BS_num; i++){
		X[i] += normal()*6.8*sqrt(t);
		Y[i] += normal()*6.8*sqrt(t);
		X[i] = max(X[i], 0.0);
		X[i] = min(X[i], 1.0*L);
		Y[i] = max(Y[i], 0.0);
		Y[i] = min(Y[i], 1.0*L);	
	}
	for(int i = 0;i < N; i++)
		for (int j = 0;j < N; j++)
			h[i][j] = rayleigh();
	for(int i = 0; i < N; i++){
		for(int j = 0; j < N; j++){
			dis[i][j] = sqrt((X[i]-X[j])*(X[i]-X[j]) + (Y[i]-Y[j])*(Y[i]-Y[j]));
			if(j < N-BS_num)
				T[i][j] = M/(B*log(1+p/noise/pow(dis[i][j], 4)));
		}	
	}
	for(int i = 0; i < N; i++) dis[i][N] = dis[N][i] = inf;
	for(int i = 0; i < N; i++){
		C[i] = 0;
		vis[i] = 0;
		exist_s[i] = exist_r[i] = skip_s[i] = skip_r[i] = 0;
		f[i] = 0;
	}
	accumulation = 0;
	disconnect = 0;
	vis[N] = 1; 
}

 

double MST(int x){
	f[x] = 1;
	int from = -1, to = -1;
	double mint = inf;
	for(int i = 0; i < N; i++){
		if(!f[i]) continue;	
		for(int j = 0; j < N; j++){
			if(f[j]) continue;
			if(T1[i][j] < mint) {
				from = i;
				to = j;
				mint = T1[i][j];
			}
		}	
	}
	if(from >= 0){
		double tmp = M/(B*log(1+h[from][to]*p/noise/pow(dis[from][to], 4)));
		if(tmp > 3*T1[from][to]) {
			dcnt++;
			tmp = T1[from][to];
		}
		return MST(to) + tmp;
	}
	
}

double Stars(){
	for(int i = 0; i < N-BS_num; i++){
		double minT = inf;
		double tmp;
		int k = 0;
		for(int j = N-BS_num; j < N; j++){
			if(T[j][i] < minT) {
				minT = T[j][i];
				tmp = T1[j][i];
				k = j;
			}
		}
		C[k] += tmp;
	}
	double ans = 0, tmp;
	tmp = max(C[N-BS_num],C[N-BS_num+2]);
	tmp = max(tmp, C[N-BS_num+6]);
	tmp = max(tmp, C[N-BS_num+8]);
	ans += tmp;
	tmp = max(C[N-BS_num+1], C[N-BS_num+3]);
	tmp = max(tmp, C[N-BS_num+5]);
	tmp = max(tmp, C[N-BS_num+7]);
	ans += tmp;
	ans += C[N-BS_num + 4];
	return ans;
}



double Star(){
	double ans = 0;
	for(int i = 0; i < N-BS_num; i++)
		ans += T[N-BS_num + 4][i];
	return ans;
}

double backup(Node* node, double res){
	if(node->r != rd){
		node->x *= pow(gamma, rd-node->r);
		node->num = 0;
		node->r = rd;
	}
	node->x += (1-pow(gamma, rd-node->r))*res;
	node->num++;
	Node* fnode = node;
	while(fnode->f != NULL){
		if(res < best_so_far){
			fnode->f->sw = fnode->w;
			fnode->f->su = fnode->u;
			fnode->f->sv = fnode->v;
		}
		fnode = fnode->f;
		if(fnode->r != rd){
			fnode->x *= pow(gamma, rd-fnode->r);
			fnode->num = 0;
			fnode->r = rd;
		}
		fnode->num++;
		fnode->x += (1-pow(gamma, rd-node->r))*res;	
	}
}
double h1[maxn][maxn];

void simulate(Node* node){
	if(node->u == N) return;
	simulate(node->f);
	if(!node->w){
		if(node->u != N) {
			rest[node->u][node->v] = M;
			h1[node->u][node->v] = h[node->u][node->v];
			if((T[node->u][node->v] > 3*T1[node->u][node->v])&& query) {
				disconnect ++;
				rest[node->u][node->v] = 3*T1[node->u][node->v]*log(1+h[node->u][node->v]*p/pow(dis[node->u][node->v], 4)/noise)*B;
			} 
		}
		return;
	}
	if(node->w){
		for(int i = 0; i < N; i++) sumI[i] = 0;
		Node* fnode = node->f;
		Node* gnode = node->f;
	
		while(gnode->u != N){
			while(fnode->u != N){
				if(!fnode->w && rest[fnode->u][fnode->v] > 1e-5 && fnode->u != gnode->u)
					sumI[gnode->u] += (query ? h1[fnode->u][fnode->v] : 1.3)*p/pow(dis[gnode->u][fnode->v], 4);
					
				fnode = fnode->f;
			}
			gnode = gnode->f;
		}
		fnode = node->f;
		double minRest = inf;
		while(fnode->u != N){
			if(!fnode->w && rest[fnode->u][fnode->v] > 1e-5){
				double tmp = (query ? h1[fnode->u][fnode->v] : 1.3)/pow(dis[fnode->u][fnode->v],4);
				double resTime = rest[fnode->u][fnode->v]/B/log(1+tmp/(noise+sumI[fnode->u])); 
				minRest = min(minRest, resTime);
			}
			fnode = fnode->f;
		}
		fnode = node->f;
		while(fnode->u != N){
			if(!fnode->w && rest[fnode->u][fnode->v] > 1e-5){
				double tmp = (query ? h1[fnode->u][fnode->v] : 1.3)/pow(dis[fnode->u][fnode->v],4);
				rest[fnode->u][fnode->v] -= minRest*B*log(1+tmp/(noise+sumI[fnode->u]));
			}
			fnode = fnode->f;
		}
		accumulation += minRest;
		return;	
	} 
}

void wait_untill_end(Node* node){
	Node* fnode = node->f;
	int cnt = 0;
	while(fnode->u != N) {
		cnt += (fnode->w == 1);
		fnode = fnode->f;
	} 
	for(int i = 0; i < N-1-BS_num-cnt; i++) {
		Node* tmpNode = new Node(1, -1, -1, rd);
		tmpNode->f = node;
		node = tmpNode;
	}
	disconnect = 0;
	accumulation = 0;
	simulate(node);
	for(int i = 0; i < N-1-BS_num-cnt; i++) {
		Node* tmpNode = node->f;
		delete node;
		node = tmpNode;
	}
	if(query == 0) backup(node, accumulation);
	if(query == 1) {
		dcnt = disconnect;
		best_so_far = accumulation;
	}
}

void getValid(Node* node){
	accumulation = 0;
	for(int u = 0; u < N; u++)
		for(int v = 0; v < N; v++) 
			rest[u][v] = 0;
	simulate(node);
	for(int u = 0; u < N; u++){
		exist_s[u] = 0;
		exist_r[u] = 0;
		for(int v = 0; v < N; v++){
			exist_s[u] |= (rest[u][v] > 1e-5);
			exist_r[u] |= (rest[v][u] > 1e-5);
		}
	}
	for(int u = 0; u < N; u++){
		skip_s[u] = 0;
		skip_r[u] = 0;
		for(int v = 0; v < N; v++){
			skip_s[u] |= (exist_r[v] && dis[u][v] < minD);
			skip_r[u] |= (exist_s[v] && dis[v][u] < minD);
		}
	}
}


void explore(Node* node){
	int done = 1;
	for(int i = 0; i < N; i++) 
		done &= vis[i];
	if(done){
		wait_untill_end(node);
		return;
	}
	getValid(node);
	double sum = 0;
	for(int u = 0; u < N; u++){
		if(!vis[u]) continue;	
		if(skip_s[u]) continue;
		for(int v = 0; v < N; v++){
			if(vis[v]) continue;
			if(skip_r[v]) continue;
			if(node->u != N && node->u*N+node->v > u*N+v) continue;
			sum += 1.0/pow(dis[u][v], beta);
		}
	}	
	if(sum == 0) {
		Node* tmpNode = new Node(1, -1, -1, rd);
		tmpNode->f = node; 
		explore(tmpNode);
		delete tmpNode;
		return;
	} 
	double r = rand()/double(RAND_MAX), s = 0;
	for(int u = 0; u < N; u++){
		if(!vis[u]) continue;
		if(skip_s[u]) continue;
		for(int v = 0; v < N; v++){
			if(vis[v]) continue;
			if(skip_r[v]) continue;
			if(node->u != N && node->u*N+node->v > u*N+v) continue;
			s += (1.0/pow(dis[u][v], beta))/sum;
			if(s > r) { 
				Node* tmpNode = new Node(0, u, v, rd);
				tmpNode->f = node;
				vis[v] = 1;
				explore(tmpNode);
				vis[v] = 0;
				delete tmpNode;
				return;
			}
		}
	}	
}


void expand(Node *node){
	for(int i = 0; i < N; i++) vis[i] = 0;
	Node *fnode;
	fnode = node;
	while(fnode != NULL){
		if(!fnode->w) vis[fnode->v] = 1;
		fnode = fnode->f;
	}
	getValid(node);
	int w = 1;
	for(int u = 0; u < N; u++){
		if(!vis[u]) continue;
		if(skip_s[u]) continue;
		for(int v = 0; v < N; v++){
			if(skip_r[v]) continue;
			if(vis[v]) continue;	
			if(node->u < N-BS_num && node->u*N+node->v > u*N+v) continue;
			if(dis[u][v] > maxD && u < N-BS_num && v < N-BS_num) continue;
			if(u != N && dis[u][v] > maxD2) continue;
 			w = 0;
			Node* newNode = new Node(0, u, v, rd);
			newNode->f = node;
			vis[v] = 1;
			explore(newNode);
			vis[v] = 0;
			if(!query) node->ch.push_back(newNode);
		}
	}
	if(!w) return;
	Node* newNode = new Node(1, -1, -1, rd);
	newNode->f = node;
	explore(newNode);
	if(!query) node->ch.push_back(newNode);
}

void MCTS(Node* node){
	for(int i = 0; i < N; i++) vis[i] = 0;
	Node *fnode;
	fnode = node;	
	while(fnode != NULL){
		vis[fnode->v] = 1;
		fnode = fnode->f;
	}	
	int done = 1;
	for(int i = 0; i < N; i++) done &= vis[i];
	if(done){
		wait_untill_end(node);
		return;
	}
	if(node->ch.empty()){
		expand(node);
		return;
	}	
	double min_score = inf;
	int I = 0;
	for(int i = 0; i < node->ch.size(); i++){
		double score = node->ch[i]->x/node->ch[i]->num;
		if(node->r == rd)
			score -= mst*sqrt(log(2*node->num)/node->ch[i]->num);
		else 
			score -= mst;
		if(score < min_score){
			min_score = score;
			I = i;
		}
	}
	MCTS(node->ch[I]);
}


clock_t start_c, end_c;
double cpu_time_used;
int stage = 0;
void solve(Node* node){	
	for(int i = 0; i < budget; i++){
		MCTS(node);
		end_c = clock();  
    	cpu_time_used = ((double) (end_c - start_c)) / CLOCKS_PER_SEC;
    	if(cpu_time_used > 2*best_so_far) return;
	}
	if(node->ch.size() > 0){
		double minExp = inf; 
		int I = 0;
		for(int i = 0; i < node->ch.size(); i++){
			if(node->ch[i]->x/node->ch[i]->num < minExp) {
				minExp = node->ch[i]->x/node->ch[i]->num;
				I = i;
			}
		}
		solve(node->ch[I]);
	}

}

int main(){
	srand((unsigned)time(NULL));
	double SS=0, SM=0, ST=0, SDM = 0, SDT = 0;
	for(int t = 0; t < 50; t++){
		init();
		Node* root = new Node(0, N, N, rd);
		Node* node = root;
		for(int i = N-BS_num; i < N; i++) {
			Node* newNode = new Node(0, N, i, rd);
			newNode->f = node;
			node->ch.push_back(newNode);
			node = newNode;
		}
		double sumMST = 0;
		double sumStar = 0;
		double sumUCT = 0;
		double sumDM = 0;
		double sumDT = 0;
		for(rd = 0; rd < 10/MM+(10%MM>0); rd++){
			cout << M << endl;
			for(int i = 0; i < N; i++) 
				for(int j = 0; j < N; j++)
					T1[i][j] = T[i][j]; 
			
			if(!rd) dynamic(M);
			if(rd) dynamic(mst);
			sumStar += Stars();
			dcnt = 0;
			for(int i = N-BS_num; i < N; i++) f[i] = 1;
			mst = MST(0);
			sumMST += mst;
			sumDM += dcnt;		
//			if(!rd) {budget = 3; query = 0; best_so_far = 2*M; solve(node); dynamic(cpu_time_used);}
//			else{
//				dynamic(best_so_far);
//				if(rd == 10/MM+(10%MM>0)) break;
//				start_c = clock();
//				budget = 3; query = 0; solve(node);
//			}
//			dcnt = 0;
//			best_so_far = inf;
//			budget = 1; query = 1; solve(node); sumDT += dcnt; sumUCT += best_so_far;
//			//cout << cpu_time_used << endl;
//			cout << dcnt << " " << best_so_far << endl;
			if(rd+1 == 10/MM && 10%M) M = 10%MM;
			else M = MM;
		}
		delete(node);
		SS += sumStar; 
		SM += sumMST;
		ST += sumUCT;
		SDM += sumDM;
		SDT += sumDT;
	}
	cout << SDM/(10/MM+(10%MM>0))/(N-9)/50 << endl;
	cout << SDT/(10/MM+(10%MM>0))/(N-9)/50 << endl;
	cout << SS/50 << " " << SM/50 << " " << ST/50 << endl;
	return 0;
}

 

