#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

// Finite domain for the comparison protocol (Section 3.1): S=4,a=2,delta=1/2,B=B'=8;
// t=2,3,4; every column-sum vector and every T=-1,...,255*t+1.
// Counts are exact integers. No random seed or input sampling occurs.
using U = uint64_t;
constexpr int S=4, K=2048;

U ipow(U b,int e) { U v=1; while(e--)v*=b; return v; }
struct Level { int width, base, count, cap; U den; std::vector<int> sums; std::vector<U> ones; };
struct Kernel { std::array<int,5> ways{}; };

std::vector<int> primes() {
    std::vector<int> all, out;
    for(int n=2;int(out.size())<K;++n) {
        bool ok=true;
        for(int p:all) { if(p*p>n)break; if(n%p==0){ok=false;break;} }
        if(ok) { all.push_back(n); if(n>S)out.push_back(n); }
    }
    return out;
}

int sumcols(int code,int w,int base) {
    int val=0;
    for(int j=0;j<w;++j){val+=(code%base)<<j;code/=base;}
    return val;
}

U get(const Level& d,int code,int target) {
    if(target<0)return d.den;
    if(target>=d.cap)return 0;
    return d.ones[U(code)*d.cap+target];
}

std::vector<Kernel> kernels(int t,int width,const std::vector<int>& ps,U& checked,U& disjoint) {
    const int shift=1<<(width/2), highcap=t*(shift-1), targetcount=(t*((1<<width)-1)-1)/shift+1;
    std::vector<Kernel> table((highcap+1)*targetcount);
    for(int sh=0;sh<=highcap;++sh)for(int th=0;th<targetcount;++th) {
        auto& k=table[sh*targetcount+th];
        int truth=th-sh;
        if(truth>=0 && truth<t)k.ways[truth]=K;
        else {
            for(int h=0;h<t;++h) {
                int diff=sh-th+h;
                if(diff==0)throw std::runtime_error("zero false difference");
                for(int p:ps)if(diff%p==0)++k.ways[h];
            }
            int bad=0;for(int h=0;h<t;++h)bad+=k.ways[h];
            k.ways[t]=K-bad;
        }
        // Independent direct modular branch enumeration for the full family.
        std::array<int,5> direct{};
        for(int p:ps) {
            int h=((th-sh)%p+p)%p;
            ++direct[h<t?h:t];
            int matches=0;for(int q=0;q<t;++q)matches+=((sh-th+q)%p==0);
            if(matches>1)throw std::runtime_error("false-h collision sets overlap");
            ++disjoint;
        }
        if(direct!=k.ways)throw std::runtime_error("kernel mismatch");
        ++checked;
    }
    return table;
}

Level baselevel(int t) {
    Level out{1,t+1,t+1,t,1,{}, {}};
    out.sums.resize(out.count);out.ones.resize(out.count*out.cap);
    for(int c=0;c<out.count;++c){out.sums[c]=c;for(int q=0;q<out.cap;++q)out.ones[c*out.cap+q]=(c>q);}
    return out;
}

Level nextlevel(int t,const Level& child,const std::vector<int>& ps,U& checked,U& disjoint) {
    int w=child.width*2, shift=1<<child.width;
    Level out{w,t+1,int(ipow(t+1,w)),t*((1<<w)-1),child.den*K,{}, {}};
    out.sums.resize(out.count);out.ones.resize(U(out.count)*out.cap);
    auto ks=kernels(t,w,ps,checked,disjoint);
    const int targetcount=(out.cap-1)/shift+1;
    for(int c=0;c<out.count;++c) {
        int lo=c%child.count,hi=c/child.count,sh=child.sums[hi];
        out.sums[c]=(sh<<child.width)+child.sums[lo];
        for(int target=0;target<out.cap;++target) {
            int th=target/shift,tl=target%shift;
            auto& k=ks[sh*targetcount+th];
            U num=U(k.ways[t])*get(child,hi,th);
            for(int h=0;h<t;++h)if(k.ways[h])num+=U(k.ways[h])*get(child,lo,tl+h*shift);
            out.ones[U(c)*out.cap+target]=num;
            if(num>out.den)throw std::runtime_error("probability overflow");
        }
    }
    return out;
}

void emit(int t,const std::vector<int>& ps) {
    auto started=std::chrono::steady_clock::now();
    U checked=0,disjoint=0;
    auto l1=baselevel(t);auto l2=nextlevel(t,l1,ps,checked,disjoint);auto l4=nextlevel(t,l2,ps,checked,disjoint);
    auto ks=kernels(t,8,ps,checked,disjoint);
    const int cap=255*t, targetcount=(cap-1)/16+1;
    const U den=ipow(K,3),classes=ipow(t+1,8);
    U maxerr=0,badstates=0,maxcount=0,states=0;
    int maxcode=0,maxtarget=0,maxtruth=0;U maxone=0;
    // This entire 8-bit level is streamed: no enormous full table is stored.
    for(int hi=0;hi<l4.count;++hi)for(int lo=0;lo<l4.count;++lo) {
        const int sh=l4.sums[hi], sum=16*sh+l4.sums[lo],code=lo+l4.count*hi;
        for(int target=0;target<cap;++target) {
            const int th=target/16,tl=target%16;
            const auto& k=ks[sh*targetcount+th];
            U num=U(k.ways[t])*get(l4,hi,th);
            for(int h=0;h<t;++h)if(k.ways[h])num+=U(k.ways[h])*get(l4,lo,tl+16*h);
            if(num>den)throw std::runtime_error("top probability overflow");
            const bool truth=sum>target;U err=truth?den-num:num;
            ++states;badstates+=(err!=0);
            if(err>maxerr){maxerr=err;maxcode=code;maxtarget=target;maxtruth=truth;maxone=num;maxcount=1;}
            else if(err==maxerr)++maxcount;
        }
    }
    if(states!=classes*cap)throw std::runtime_error("coverage mismatch");
    std::vector<int> cols(8),xs(t);
    int tmp=maxcode;for(int j=0;j<8;++j){cols[j]=tmp%(t+1);tmp/=(t+1);for(int i=0;i<cols[j];++i)xs[i]|=1<<j;}
    U g=std::gcd(maxerr,den);
    auto duration=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
    std::cout << "{\"t\":"<<t<<",\"column_classes\":"<<classes<<",\"represented_ordered_input_tuples\":"<<ipow(256,t)
              <<",\"thresholds_per_class\":"<<cap+3<<",\"nontrivial_states_checked\":"<<states
              <<",\"boundary_states_checked_symbolically\":"<<3*classes<<",\"nonzero_error_states\":"<<badstates
              <<",\"kernel_cases_cross_checked\":"<<checked<<",\"prime_disjointness_checks\":"<<disjoint
              <<",\"worst_error_numerator\":"<<maxerr<<",\"seed_denominator\":"<<den
              <<",\"reduced_numerator\":"<<maxerr/g<<",\"reduced_denominator\":"<<den/g
              <<",\"maximizer_count\":"<<maxcount<<",\"witness\":{\"columns_lsb_first\":[";
    for(int j=0;j<8;++j){if(j)std::cout<<",";std::cout<<cols[j];}
    std::cout<<"],\"party_inputs\":[";for(int i=0;i<t;++i){if(i)std::cout<<",";std::cout<<xs[i];}
    std::cout<<"],\"threshold\":"<<maxtarget<<",\"true_output\":"<<maxtruth<<",\"output_one_seed_count\":"<<maxone
             <<"},\"seconds\":"<<duration<<"}";
}

int main(int argc,char** argv) {
    const int J=3,Bp=8,a=2; const int required=4*J*S*(Bp+2+3)*2;
    if(!(K>=required && K/2<required && Bp<=int(ipow(S,a))))throw std::runtime_error("parameter contract failed");
    auto ps=primes();
    std::cout<<"{\"S\":4,\"a\":2,\"delta\":\"1/2\",\"B_prime\":8,\"J\":3,\"required_K\":"<<required
             <<",\"K\":"<<K<<",\"seed_bits\":33,\"prime_min\":"<<ps.front()<<",\"prime_max\":"<<ps.back()<<",\"results\":[";
    bool first=true;
    for(int t=2;t<=4;++t){if(argc>1 && std::stoi(argv[1])!=t)continue;if(!first)std::cout<<",";first=false;emit(t,ps);}
    std::cout<<"]}\n";
}
