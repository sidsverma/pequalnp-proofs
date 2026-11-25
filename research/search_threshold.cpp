#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using Bits=__uint128_t;
struct Gate{int a,b,op;};
std::mt19937 rng(10453);
int pick(int n){return rng()%n;}
int pop(Bits x){return __builtin_popcountll((uint64_t)x)+__builtin_popcountll((uint64_t)(x>>64));}
int main(int argc,char**argv){
 int targetSize=argc>1?atoi(argv[1]):15,limit=argc>2?atoi(argv[2]):300,allowNot=argc>3?atoi(argv[3]):1;
 std::array<Bits,7> inputs{};Bits target=0,critical=0;
 for(int x=0;x<128;++x){for(int i=0;i<7;++i)if(x>>i&1)inputs[i]|=Bits(1)<<x;if(__builtin_popcount(x)>=2)target|=Bits(1)<<x;if(__builtin_popcount(x)<=2)critical|=Bits(1)<<x;}
 std::vector<Gate> baseline;
 auto add=[&](int a,int b,int op){baseline.push_back({a,b,op});return 6+(int)baseline.size();};
 int any=add(0,1,1),two=add(0,1,0);
 for(int i=2;i<7;++i){int cross=add(any,i,0);two=add(two,cross,1);if(i<6)any=add(any,i,1);}
 auto error=[&](const std::vector<Gate>& gs){std::array<Bits,40> vals{};for(int i=0;i<7;++i)vals[i]=inputs[i];for(int i=0;i<(int)gs.size();++i){auto g=gs[i];vals[7+i]=g.op==0?(vals[g.a]&vals[g.b]):g.op==1?(vals[g.a]|vals[g.b]):~vals[g.a];}Bits diff=vals[6+gs.size()]^target;return pop(diff)+15*pop(diff&critical);};
 if(error(baseline)){std::cerr<<"bad baseline\n";return 2;}
 auto usedNot=[&](const std::vector<Gate>& gs){std::array<bool,40> used{};used[6+gs.size()]=true;bool found=false;for(int i=(int)gs.size()-1;i>=0;--i)if(used[7+i]){auto g=gs[i];used[g.a]=true;if(g.op!=2)used[g.b]=true;else found=true;}return found;};
 int best=100000;uint64_t trials=0;auto start=std::chrono::steady_clock::now();
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<limit){
   auto gs=baseline;
   while((int)gs.size()>targetSize){int drop=pick(gs.size()-1),rep=pick(2)?gs[drop].a:gs[drop].b;gs.erase(gs.begin()+drop);for(auto& g:gs)for(int* w:{&g.a,&g.b}){if(*w==7+drop)*w=rep;if(*w>7+drop)--*w;}}
   if(allowNot)gs[pick(gs.size()-1)].op=2;
   if(allowNot&&!usedNot(gs))continue;
   int err=error(gs),stuck=0;
   for(int step=0;step<100000 && stuck<15000;++step){
     auto cand=gs;int count=1+(pick(15)==0)+(pick(100)==0);
     for(int j=0;j<count;++j){int g=pick(cand.size()),field=pick(3);if(field==0)cand[g].a=pick(7+g);else if(field==1)cand[g].b=pick(7+g);else cand[g].op=pick(allowNot?3:2);}
     int negs=0;for(auto g:cand)negs+=g.op==2;if(negs!=allowNot)continue;
     if(allowNot&&!usedNot(cand))continue;
     int ne=error(cand);++trials;
     if(ne<=err){stuck=ne<err?0:stuck+1;gs=std::move(cand);err=ne;}else ++stuck;
     if(err<best){best=err;std::cout<<"best weighted mismatch "<<err<<" after "<<trials<<"\n"<<std::flush;std::ofstream f("threshold-best-s"+std::to_string(targetSize)+"-not"+std::to_string(allowNot)+".txt");f<<7<<" "<<targetSize<<"\n";for(auto g:gs)f<<(g.op==0?"and":g.op==1?"or":"not")<<" "<<g.a<<" "<<g.b<<"\n";}
     if(err==0){std::string name="threshold-witness-s"+std::to_string(targetSize)+"-not"+std::to_string(allowNot)+".txt";std::ofstream f(name);f<<7<<" "<<targetSize<<"\n";for(auto g:gs)f<<(g.op==0?"and":g.op==1?"or":"not")<<" "<<g.a<<" "<<g.b<<"\n";std::cout<<"Verified all 128 inputs; witness "<<name<<"\n";return 0;}
   }
 }
 std::cout<<"Finished "<<trials<<" trials, best mismatch "<<best<<"\n";
}
