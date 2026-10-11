using System.Diagnostics;
using System.Numerics;
using System.Text.Json;

// Mixed-radix arithmetic and exhaustive search.
// All saved witnesses also pass the independent coordinate checker below.
sealed class Group {
 public int[] D; public int N; public int[,] Sum; public int[] Neg;
 public string Name => string.Join("x",D.Select(x=>"Z"+x));
 public Group(params int[] dims) {
  D=dims;N=dims.Aggregate(1,(a,b)=>a*b);Sum=new int[N,N];Neg=new int[N];
  for(int a=0;a<N;a++)for(int b=0;b<N;b++){
   int x=a,y=b,p=1,s=0;foreach(int m in D){s+=(x%m+y%m)%m*p;x/=m;y/=m;p*=m;}
   Sum[a,b]=s;if(s==0)Neg[a]=b;
  }
 }
 public int Sub(int a,int b)=>Sum[a,Neg[b]];
 public int Add(params int[] a)=>a.Aggregate(0,(x,y)=>Sum[x,y]);
 public int Order(int a){int x=a,n=1;while(x!=0){x=Sum[x,a];n++;}return n;}
 public int Mul(int a,int k){if(k<0)return Mul(Neg[a],-k);int s=0;while(k-->0)s=Sum[s,a];return s;}
 public int[] All=>Enumerable.Range(0,N).ToArray();
}
static class Check {
 public static void Assert(bool v,string why){if(!v)throw new Exception(why);}
 public static int Add(int[] dims,int a,int b) {
  int s=0,p=1;foreach(int m in dims){s+=((a/p%m+b/p%m)%m)*p;p*=m;}return s;
 }
 public static int[] Cycle(Group g,int[] holes,int[] cycle) {
  var a=g.All.Except(holes).ToArray();
  Assert(a.Length>2&&cycle.Length==a.Length,"length");
  Assert(cycle.Distinct().Count()==a.Length&&cycle.Order().SequenceEqual(a),"coverage");
  var colors=Enumerable.Range(0,cycle.Length).Select(i=>Add(g.D,cycle[i],cycle[(i+1)%cycle.Length])).ToArray();
  Assert(colors.Distinct().Count()==cycle.Length,"rainbow");
  return g.All.Except(colors).ToArray();
 }
}
static class Independent {
 public static void Assert(bool v,string why)=>Check.Assert(v,why);
 public static int Add(int[] dims,int a,int b)=>Check.Add(dims,a,b);
 public static void Cycle(Group g,int[] a,int[] c) {
  Check.Assert(c.Length>=3&&c.Order().SequenceEqual(a.Order())&&c.Distinct().Count()==a.Length,"cycle coverage");
  Check.Assert(Enumerable.Range(0,c.Length).Select(i=>Check.Add(g.D,c[i],c[(i+1)%c.Length])).Distinct().Count()==c.Length,"cycle rainbow");
 }
}
sealed class Search {
 readonly Group g;readonly Random rng=new(20261011);
 int[] p=[],order=[];ulong forbidden;long nodes,budget;bool stopped;
 public Search(Group g){this.g=g;Check.Assert(g.N<=63,"bitset group bound");}
 bool Dfs(int depth,ulong remaining,ulong used){
  if(++nodes>budget){stopped=true;return false;}
  int last=p[depth-1];
  if(remaining==0)return ((used|forbidden)&(1UL<<g.Sum[last,p[0]]))==0;
  foreach(int v in order) {
   ulong b=1UL<<v;if((remaining&b)==0)continue;
   ulong color=1UL<<g.Sum[last,v];if(((used|forbidden)&color)!=0)continue;
   p[depth]=v;if(Dfs(depth+1,remaining^b,used|color))return true;
   if(stopped)return false;
  }return false;
 }
 public (string status,int[]? cycle,long nodes) Solve(int[] holes,int[]? missing=null,long limit=100000,int tries=100){
  int[] a=g.All.Except(holes).ToArray();
  if(missing!=null&&missing.Distinct().Count()!=holes.Length)return("COLLISION",null,0);
  forbidden=0;if(missing!=null)foreach(int v in missing)forbidden|=1UL<<v;
  long total=0;
  for(int t=0;t<tries;t++){
   order=(int[])a.Clone();if(t>0)rng.Shuffle(order);
   p=new int[a.Length];p[0]=a[0];ulong rem=0;foreach(int v in a.Skip(1))rem|=1UL<<v;
   nodes=0;budget=limit;stopped=false;bool ok=Dfs(1,rem,0);total+=nodes;
   if(ok){var absent=Check.Cycle(g,holes,p);if(missing!=null)Check.Assert(absent.Order().SequenceEqual(missing.Order()),"exact colors");return("FOUND",p,total);}
   if(!stopped)return("EXHAUSTIVE_FAILURE",null,total);
  }return("UNKNOWN",null,total);
 }
}
static class Program {
 public static void Save(StreamWriter f,object row){f.WriteLine(JsonSerializer.Serialize(row));f.Flush();}
 public static IEnumerable<Group> Groups(int max=35){
  var groups=new List<Group>();for(int n=7;n<=max;n+=2)groups.Add(new Group(n));
  foreach(int[] dims in new[]{new[]{3,3},new[]{5,5},new[]{3,9},new[]{3,3,3},new[]{3,15},new[]{7,7},new[]{3,21}})
   if(dims.Aggregate(1,(a,b)=>a*b)<=max)groups.Add(new Group(dims));
  Check.Assert(max<=63,"classification list bound");
  return groups.OrderBy(g=>g.N).ThenBy(g=>g.Name);
 }
 static string Key(params int[] h)=>string.Join(",",h.Order());
 static void Baseline(int max,int min=7){
  var watch=Stopwatch.StartNew();var rows=new List<object>();
  using var log=new StreamWriter($"baseline-{min}-{max}.jsonl");
  using var w=new StreamWriter($"witnesses-{min}-{max}.jsonl");
  using var pending=new StreamWriter($"pending-{min}-{max}.jsonl");
  foreach(var g in Groups(max).Where(g=>g.N>=min)){
   var timer=Stopwatch.StartNew();var search=new Search(g);var cache=new Dictionary<string,int[]>();
   int count=0,fail=0,unknown=0;long nodes=0;
   for(int d=1;d<g.N;d++)for(int e=d+1;e<g.N;e++)for(int f=e+1;f<g.N;f++){
    int[] holes={0,d,e,f};var r=search.Solve(holes);nodes+=r.nodes;count++;
    if(r.cycle!=null){cache.Add(Key(d,e,f),r.cycle);Save(w,new{group=g.Name,dims=g.D,holes,cycle=r.cycle,missing=Check.Cycle(g,holes,r.cycle),r.nodes});}
    else{if(r.status=="EXHAUSTIVE_FAILURE")fail++;else unknown++;Save(pending,new{group=g.Name,holes,r.status,r.nodes});Console.WriteLine(JsonSerializer.Serialize(new{ALERT=r.status,group=g.Name,holes}));}
    if(count%1000==0)Save(log,new{stage="search",group=g.Name,count,fail,unknown,nodes,seconds=timer.Elapsed.TotalSeconds});
   }
   long raw=0,verified=0;
   for(int a=0;a<g.N;a++)for(int b=a+1;b<g.N;b++)for(int c=b+1;c<g.N;c++)for(int d=c+1;d<g.N;d++){
    raw++;if(!cache.TryGetValue(Key(g.Sub(b,a),g.Sub(c,a),g.Sub(d,a)),out var cyc))continue;
    var translated=cyc.Select(x=>g.Sum[x,a]).ToArray();Check.Cycle(g,new[]{a,b,c,d},translated);verified++;
   }
   Check.Assert(raw==(long)g.N*(g.N-1)*(g.N-2)*(g.N-3)/24,"raw coverage");
   var row=new{stage="group-complete",group=g.Name,dims=g.D,order=g.N,normalized=count,allFourSets=raw,verified,normalizedCounterexamples=fail,normalizedUnknown=unknown,nodes,seconds=timer.Elapsed.TotalSeconds};
   rows.Add(row);Save(log,row);Console.WriteLine(JsonSerializer.Serialize(row));
   File.WriteAllText($"baseline-summary-{min}-{max}.json",JsonSerializer.Serialize(new{completed=false,groups=rows,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
  }
  File.WriteAllText($"baseline-summary-{min}-{max}.json",JsonSerializer.Serialize(new{completed=true,groups=rows,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
 }
 static void Audit(string path){
  var watch=Stopwatch.StartNew();long count=0,edges=0;var seen=new HashSet<string>();var counts=new Dictionary<string,int>();
  foreach(string line in File.ReadLines(path)){
   using var j=JsonDocument.Parse(line);var r=j.RootElement;
   int[] Read(string k)=>r.GetProperty(k).EnumerateArray().Select(x=>x.GetInt32()).ToArray();
   var g=new Group(Read("dims"));var holes=Read("holes");var cycle=Read("cycle");
   var m=Check.Cycle(g,holes,cycle);
   Check.Assert(m.SequenceEqual(Read("missing")),"recorded missing");
   Check.Assert(holes.Length==4&&holes[0]==0&&holes.Distinct().Count()==4,"hole form");
   Check.Assert(seen.Add(g.Name+":"+Key(holes)),"duplicate");
   counts[g.Name]=counts.GetValueOrDefault(g.Name)+1;count++;edges+=cycle.Length;
  }
  foreach(var p in counts){int n=p.Key.Split('x').Select(x=>int.Parse(x[1..])).Aggregate(1,(a,b)=>a*b);Check.Assert(p.Value==(n-1)*(n-2)*(n-3)/6,"normalized coverage");}
  var result=new{completed=true,pass=true,path,groups=counts,count,edges,seconds=watch.Elapsed.TotalSeconds};Console.WriteLine(JsonSerializer.Serialize(result));
  File.WriteAllText("audit-"+Path.GetFileNameWithoutExtension(path)+".json",JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true}));
 }
 public static void Main(string[] args){
  if(args.Length>0&&args[0]=="structure"){StructuralTests.Run();return;}
  if(args.Length>0&&args[0]=="extra"){StructuralTests.Extra();return;}
  if(args.Length>0&&args[0]=="construct"){FourConstructor.Run(args.Length>1?int.Parse(args[1]):35);return;}
  if(args.Length>0&&args[0]=="cyclic-test"){FourConstructor.CyclicTest();return;}
  if(args.Length>0&&args[0]=="glue"){GeneralGlue.Run(args.Length>1?int.Parse(args[1]):35);return;}
  if(args.Length>0&&args[0]=="audit"){Audit(args[1]);return;}
  if(args.Length>0&&args[0]=="baseline"){Baseline(args.Length>1?int.Parse(args[1]):35,args.Length>2?int.Parse(args[2]):7);return;}
  Baseline(35);
 }
}

