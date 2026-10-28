#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;

static long long det(vector<vector<long long>> a) {
    int n=a.size(); if(!n) return 1;
    long long prev=1,sgn=1;
    for(int k=0;k<n-1;k++){
        int p=k; while(p<n && a[p][k]==0) p++;
        if(p==n) return 0;
        if(p!=k){ swap(a[p],a[k]);sgn=-sgn; }
        long long pivot=a[k][k];
        for(int i=k+1;i<n;i++) for(int j=k+1;j<n;j++){
            long long val=a[i][j]*pivot-a[i][k]*a[k][j];
            assert(val%prev==0);a[i][j]=val/prev;
        }
        for(int i=k+1;i<n;i++)a[i][k]=0;
        prev=pivot;
    }
    return sgn*a[n-1][n-1];
}
static vector<int> labels(int n,int mask){
    vector<int> b(n);for(int i=1;i<n;i++)b[i]=b[i-1]+((mask>>(i-1))&1);return b;
}
static void sign_audit(){
    uint64_t checks=0;
    for(int n=1;n<=7;n++){
        vector<int> p(n);iota(p.begin(),p.end(),0);
        int np=1<<(n-1);
        do{
            int inv=0;vector<int> pinv(n);
            for(int i=0;i<n;i++){pinv[p[i]]=i;for(int j=0;j<i;j++) inv+=p[j]>p[i];}
            for(int rm=0;rm<np;rm++){
                auto R=labels(n,rm);int nr=R.back()+1;
                for(int cm=0;cm<np;cm++){
                    auto C=labels(n,cm);int nc=C.back()+1;
                    int ir=0,ic=0,cell=0,cross=0;
                    vector<vector<int>> cnt(nr,vector<int>(nc));
                    for(int i=0;i<n;i++)cnt[R[i]][C[p[i]]]++;
                    for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
                        if(R[i]==R[j]){
                            ir+=C[p[i]]>C[p[j]];
                            if(C[p[i]]==C[p[j]])cell+=p[i]>p[j];
                        }
                        if(C[i]==C[j])ic+=R[pinv[i]]>R[pinv[j]];
                    }
                    for(int a=0;a<nr;a++)for(int aa=a+1;aa<nr;aa++)
                        for(int b=0;b<nc;b++)for(int bb=0;bb<b;bb++)cross+=cnt[a][b]*cnt[aa][bb];
                    assert(inv==ir+ic+cell+cross);checks++;
                }
            }
        }while(next_permutation(p.begin(),p.end()));
    }
    cout<<"{\"test\":\"sign_all_permutations_all_contiguous_partitions\",\"max_n\":7,\"checks\":"<<checks<<",\"status\":\"PASS\"}"<<endl;
}
struct DSU{vector<int>p;DSU(int n):p(n){iota(p.begin(),p.end(),0);}int f(int x){return p[x]==x?x:p[x]=f(p[x]);}bool un(int x,int y){x=f(x);y=f(y);if(x==y)return false;p[x]=y;return true;}};
static void marker_audit(){
    uint64_t checks=0;
    for(int n=0;n<=5;n++){
        vector<pair<int,int>>edges;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)edges.emplace_back(i,j);
        int m=edges.size();
        for(int g=0;g<(1<<m);g++)for(int u=0;u<(1<<n);u++){
            vector<pair<int,int>>ind;for(int e=0;e<m;e++)if((g>>e&1)&&(u>>edges[e].first&1)&&(u>>edges[e].second&1))ind.push_back(edges[e]);
            for(int mark=u;;mark=(mark-1)&u){
                vector<vector<long long>>A(n,vector<long long>(n));
                for(int i=0;i<n;i++)A[i][i]=(!(u>>i&1))+(mark>>i&1);
                for(auto [i,j]:ind){A[i][i]++;A[j][j]++;A[i][j]--;A[j][i]--;}
                long long d=det(A), trees=0;
                auto aug=ind;for(int i=0;i<n;i++)if(mark>>i&1)aug.emplace_back(i,n);
                int need=__builtin_popcount((unsigned)u);
                for(int es=0;es<(1<<(int)aug.size());es++)if(__builtin_popcount((unsigned)es)==need){
                    DSU ds(n+1);bool forest=true;
                    for(int e=0;e<(int)aug.size();e++)if(es>>e&1)if(!ds.un(aug[e].first,aug[e].second)){forest=false;break;}
                    if(!forest)continue;
                    bool conn=true;for(int i=0;i<n;i++)if((u>>i&1)&&ds.f(i)!=ds.f(n))conn=false;
                    trees+=conn;
                }
                assert(d==trees);
                if((int)ind.size()+__builtin_popcount((unsigned)mark)==need){
                    DSU ds(n);bool forest=true;for(auto [i,j]:ind)if(!ds.un(i,j))forest=false;
                    vector<int>count(n);for(int i=0;i<n;i++)if(mark>>i&1)count[ds.f(i)]++;
                    bool good=forest;for(int i=0;i<n;i++)if((u>>i&1)&&count[ds.f(i)]!=1)good=false;
                    assert(d==(good?1:0));
                }
                checks++;if(mark==0)break;
            }
        }
    }
    cout<<"{\"test\":\"marker_determinant_vs_enumerated_augmented_spanning_trees\",\"max_n\":5,\"checks\":"<<checks<<",\"status\":\"PASS\"}"<<endl;
}
static void directed_audit(){
    uint64_t checks=0;
    for(int n=0;n<=4;n++){
        vector<pair<int,int>> arcs;for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j)arcs.emplace_back(i,j);
        int m=arcs.size();
        for(int g=0;g<(1<<m);g++)for(int u=0;u<(1<<n);u++){
            vector<vector<int>> out(n);
            for(int e=0;e<m;e++)if((g>>e&1)&&(u>>arcs[e].first&1)&&(u>>arcs[e].second&1))out[arcs[e].first].push_back(arcs[e].second);
            for(int mark=u;;mark=(mark-1)&u){
                vector<vector<long long>> A(n,vector<long long>(n));
                vector<vector<int>> choice=out;
                for(int i=0;i<n;i++){
                    A[i][i]=out[i].size()+(!(u>>i&1))+(mark>>i&1);
                    for(int j:out[i])A[i][j]--;
                    if(mark>>i&1)choice[i].push_back(n);
                }
                long long count=0;vector<int> f(n,-1);
                auto rec=[&](auto&& self,int i)->void{
                    if(i==n){
                        for(int v=0;v<n;v++)if(u>>v&1){
                            int seen=0,x=v;
                            while(x!=n && !(seen>>x&1)){seen|=1<<x;x=f[x];assert(x>=0);}
                            if(x!=n)return;
                        }
                        count++;return;
                    }
                    if(!(u>>i&1)){self(self,i+1);return;}
                    for(int j:choice[i]){f[i]=j;self(self,i+1);}
                };
                rec(rec,0);
                long long value=det(A);assert(value==count);
                int reachable=mark,previous=-1;
                while(reachable!=previous){previous=reachable;for(int i=0;i<n;i++)if(u>>i&1)for(int j:out[i])if(reachable>>j&1)reachable|=1<<i;}
                assert((value>0)==((reachable&u)==u));
                checks++;if(mark==0)break;
            }
        }
    }
    cout<<"{\"test\":\"directed_marker_determinant_vs_acyclic_functional_choices\",\"max_n\":4,\"checks\":"<<checks<<",\"status\":\"PASS\"}"<<endl;
}
int main(int argc,char**argv){
    auto start=chrono::steady_clock::now();
    if(argc!=2)return 2;
    if(string(argv[1])=="sign")sign_audit();else if(string(argv[1])=="marker")marker_audit();else if(string(argv[1])=="directed")directed_audit();else return 2;
    (void)start; // Runtime is recorded by the serial runner.
}
