using System.Diagnostics;
using System.Text.Json;
static class StructuralTests {
 static int Dot(int a,int b,int p,int rank){int s=0;for(int i=0;i<rank;i++){s+=a%p*(b%p);a/=p;b/=p;}return s%p;}
 static int[] Functionals(int p,int rank){
  int n=(int)Math.Pow(p,rank);
  return Enumerable.Range(1,n-1).Where(x=>{while(x%p==0)x/=p;return x%p==1;}).ToArray();
 }
 public static void Run() {
  var watch=Stopwatch.StartNew();var rows=new List<object>();
  foreach(int rank in new[]{2,3,4}){
   int n=(int)Math.Pow(3,rank);int[] maps=Functionals(3,rank);
   int[,] values=new int[maps.Length,n];for(int i=0;i<maps.Length;i++)for(int x=0;x<n;x++)values[i,x]=Dot(maps[i],x,3,rank);
   long count=0;
   for(int a=0;a<n;a++)for(int b=a;b<n;b++)for(int c=b;c<n;c++){
    bool found=false;
    for(int i=0;i<maps.Length;i++){
     int bits=1|(1<<values[i,a])|(1<<values[i,b])|(1<<values[i,c]);
     if(bits!=7){found=true;break;}
    }
    Check.Assert(found,"F3 quotient lemma");count++;
   }
   rows.Add(new{lemma="C",rank,normalizedMultisets=count,functionals=maps.Length});Console.WriteLine(JsonSerializer.Serialize(rows[^1]));
  }
  int f5=0;int[] maps5=Functionals(5,2);
  for(int a=0;a<25;a++)for(int b=a+1;b<25;b++)for(int c=b+1;c<25;c++)for(int d=c+1;d<25;d++){
   int bad=0;bool found=false;
   foreach(int ell in maps5){
    var hist=new int[5];foreach(int x in new[]{a,b,c,d})hist[Dot(ell,x,5,2)]++;
    if(hist.Max()>=3)bad++;
    if(hist.Max()<=2&&hist.Contains(0))found=true;
   }
   Check.Assert(bad<=4&&found,"F5 direction lemma");f5++;
  }
  rows.Add(new{lemma="D",allFourSets=f5,directions=maps5.Length});
  var plane=new Group(3,3);var maker=new FourConstructor(plane);int f3=0;
  for(int a=0;a<9;a++)for(int b=a+1;b<9;b++)for(int c=b+1;c<9;c++)for(int d=c+1;d<9;d++){
   int[] holes={a,b,c,d};Check.Cycle(plane,holes,maker.Build(holes));f3++;
  }
  rows.Add(new{lemma="E",allFourSets=f3});
  var bases=new[]{
   (holes:new[]{0,1,2,3},cycle:new[]{4,5,6,7,8}),
   (holes:new[]{0,1,3,4},cycle:new[]{2,5,6,8,7}),
   (holes:new[]{0,1,3,5},cycle:new[]{2,4,7,6,8}),
   (holes:new[]{0,1,3,7},cycle:new[]{2,4,5,6,8}),
   (holes:new[]{0},cycle:new[]{1,3,4,7,2,6,8,5})};
  using var bf=new StreamWriter("finite-bases.jsonl");
  foreach(var b in bases){Check.Cycle(plane,b.holes,b.cycle);Program.Save(bf,new{dims=plane.D,b.holes,b.cycle,colors=Enumerable.Range(0,b.cycle.Length).Select(i=>Check.Add(plane.D,b.cycle[i],b.cycle[(i+1)%b.cycle.Length])).ToArray()});}
  int[] cross={0,1,2,3,6};
  foreach(int ell in Functionals(3,2))Check.Assert(cross.Select(x=>Dot(ell,x,3,2)).Distinct().Count()==3,"five-hole blocking example");
  File.WriteAllText("structural-summary.json",JsonSerializer.Serialize(new{completed=true,pass=true,rows,fiveHoleBlockingExample=cross,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
 }
 public static void Extra() {
  var watch=Stopwatch.StartNew();var rows=new List<object>();var rng=new Random(41123);
  int[][] dimensions={new[]{3,15},new[]{7,7},new[]{3,21},new[]{5,15},
   new[]{3,27},new[]{9,9},new[]{3,3,9},new[]{3,3,3,3},new[]{3,33},
   new[]{3,39},new[]{11,11},new[]{5,25},new[]{5,5,5},new[]{15,15},
   new[]{3,75},new[]{5,45},new[]{3,81},new[]{9,27}};
  using var log=new StreamWriter("construction-extra.jsonl");using var w=new StreamWriter("construction-extra-witnesses.jsonl");
  foreach(int[] dims in dimensions){
   var g=new Group(dims);var maker=new FourConstructor(g);var seen=new HashSet<string>();var branches=new Dictionary<string,int>();int count=0;
   while(count<2000){
    int[] tail=Enumerable.Range(1,g.N-1).OrderBy(_=>rng.Next()).Take(3).Order().ToArray();
    string key=string.Join(",",tail);if(!seen.Add(key))continue;
    int[] holes=new[]{0}.Concat(tail).ToArray();var cycle=maker.Build(holes);Check.Cycle(g,holes,cycle);
    Program.Save(w,new{group=g.Name,dims,holes,cycle,missing=Check.Cycle(g,holes,cycle),branch=maker.Branch});
    branches[maker.Branch]=branches.GetValueOrDefault(maker.Branch)+1;count++;
   }
   Check.Cycle(g,new[]{0},maker.Build(new[]{0}));
   var row=new{group=g.Name,order=g.N,sampledNormalizedFourSets=count,branches,oneHoleCheck=true};
   rows.Add(row);Program.Save(log,row);Console.WriteLine(JsonSerializer.Serialize(row));
  }
  File.WriteAllText("construction-extra-summary.json",JsonSerializer.Serialize(new{completed=true,groups=rows,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
 }
}

