#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using Bits = __uint128_t;
struct Gate { int a, b; bool isOr; };
std::mt19937 rng(20261125);
int pick(int n) { return rng() % n; }
int pop(Bits x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
int main(int argc, char **argv) {
  int k = argc > 1 ? atoi(argv[1]) : 3;
  int seconds = argc > 2 ? atoi(argv[2]) : 300;
  bool path = argc > 3;
  int n = 3*k + path, ni=2*n;
  std::vector<Bits> inputs(ni);
  Bits goal=0;
  for(int a=0;a<n;++a) for(int b=0;b<n;++b) {
    int pos=a*n+b;
    inputs[a] |= Bits(1)<<pos;
    inputs[n+b] |= Bits(1)<<pos;
    for(int i=0;i<k;++i) {
      int u=i, v=k+path+i, w=path?i+1:(i+1)%k, z=2*k+path+i;
      if(((a==u||a==v)&&(b==w||b==z))||((b==u||b==v)&&(a==w||a==z))) goal|=Bits(1)<<pos;
    }
  }
  std::vector<Gate> base;
  auto add=[&](int a,int b,bool op){base.push_back({a,b,op});return ni+(int)base.size()-1;};
  for(int i=0;i<n;++i)add(i,n+i,true);
  std::vector<int> outs;
  for(int i=0;i<k;++i){
    int l=add(ni+i,ni+k+path+i,true);
    int r=add(ni+(path?i+1:(i+1)%k),ni+2*k+path+i,true);
    outs.push_back(add(l,r,false));
  }
  int out=outs[0];for(int i=1;i<k;++i)out=add(out,outs[i],true);
  auto error=[&](const std::vector<Gate>& gs){
    std::array<Bits,128> vals{};
    for(int i=0;i<ni;++i)vals[i]=inputs[i];
    for(int i=0;i<(int)gs.size();++i){auto g=gs[i];vals[ni+i]=g.isOr?(vals[g.a]|vals[g.b]):(vals[g.a]&vals[g.b]);}
    return pop(vals[ni+gs.size()-1]^goal);
  };
  if(error(base)!=0){std::cerr<<"invalid baseline\n";return 2;}
  int best=999;uint64_t trials=0;
  auto start=std::chrono::steady_clock::now();
  for(int restart=0;;++restart){
    if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
    int drop=pick(base.size()-1), replacement=pick(2)?base[drop].a:base[drop].b;
    auto gs=base;gs.erase(gs.begin()+drop);
    for(auto& g:gs)for(int* w:{&g.a,&g.b}){
      if(*w==ni+drop)*w=replacement;
      if(*w>ni+drop)--*w;
    }
    int e=error(gs), stuck=0;
    for(int step=0;step<100000 && stuck<12000;++step){
      auto candidate=gs;
      int count=1+(pick(12)==0)+(pick(60)==0);
      for(int j=0;j<count;++j){
        int g=pick(candidate.size()),field=pick(3);
        if(field==0)candidate[g].a=pick(ni+g);
        else if(field==1)candidate[g].b=pick(ni+g);
        else candidate[g].isOr=!candidate[g].isOr;
      }
      int ne=error(candidate);++trials;
      if(ne<=e){stuck=ne<e?0:stuck+1;gs=std::move(candidate);e=ne;}else ++stuck;
      if(e<best){best=e;std::cout<<"best "<<best<<" after "<<trials<<" trials\n"<<std::flush;}
      if(e==0){
        std::ofstream f(path?"path-witness.txt":"cycle-witness.txt");
        f<<n<<" "<<gs.size()<<"\n";
        for(auto g:gs)f<<(g.isOr?"or":"and")<<" "<<g.a<<" "<<g.b<<"\n";
        std::cout<<"Found independently evaluated witness\n";return 0;
      }
    }
  }
  std::cout<<"Finished "<<trials<<" trials, best error "<<best<<"\n";
}
