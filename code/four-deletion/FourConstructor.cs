using System.Diagnostics;
using System.Text.Json;
sealed class FourConstructor {
 readonly Group g;readonly Constructor old;readonly GeneralGlue glue;
 readonly Dictionary<string,(Group group,int[] map,int[] inverse,FourConstructor maker)> models=new();
 readonly Dictionary<string,int[]> built=new();Complete? three;
 public string Branch="";public long CyclicCases,PlaneCases,Inductions,GlueCases;
 public FourConstructor(Group g){this.g=g;old=new Constructor(g);glue=new GeneralGlue(g,LocalCycle);}
 static string Key(IEnumerable<int> a)=>string.Join(",",a.Order());
 public static int[] OddCycle(int[] sorted) {
  Check.Assert(sorted.Length>=3&&sorted.Length%2==1,"odd cyclic input");
  int l=sorted.Length/2;var ans=new List<int>{sorted[0],sorted[l]};
  for(int j=l;j>=1;j--){ans.Add(sorted[l+j]);if(j>1)ans.Add(sorted[j-1]);}
  return ans.ToArray();
 }
 (int[] dims,int[] map) Decompose(int[] h){
  if(h.Length==1)return (Array.Empty<int>(),new[]{0});
  int z=h.MaxBy(g.Order),m=g.Order(z);int[] c=old.Cyclic(z);
  int[] b=old.Subgroups.First(b=>b.Length==h.Length/m&&old.Contained(b,h)&&b.Intersect(c).Count()==1);
  var rem=Decompose(b);var dims=new[]{m}.Concat(rem.dims).ToArray();
  int[] map=rem.map.SelectMany(y=>Enumerable.Range(0,m).Select(i=>g.Add(g.Mul(z,i),y))).ToArray();
  Check.Assert(map.Distinct().Count()==h.Length&&map.Order().SequenceEqual(h),"direct-product coordinates");
  return(dims,map);
 }
 (Group group,int[] map,int[] inverse,FourConstructor maker) Model(int[] h){
  string key=Key(h);if(models.TryGetValue(key,out var model))return model;
  var (dims,map)=Decompose(h);var lg=new Group(dims);int[] inverse=Enumerable.Repeat(-1,g.N).ToArray();
  for(int i=0;i<map.Length;i++)inverse[map[i]]=i;
  for(int a=0;a<lg.N;a++)for(int b=0;b<lg.N;b++)
   Check.Assert(map[Check.Add(lg.D,a,b)]==Check.Add(g.D,map[a],map[b]),"subgroup isomorphism");
  model=(lg,map,inverse,new FourConstructor(lg));models[key]=model;return model;
 }
 int[] LocalCycle(int[] h,int[] b) {
  var model=Model(h);var holes=h.Except(b).Select(x=>model.inverse[x]).ToArray();
  int[] result=model.maker.Build(holes).Select(x=>model.map[x]).ToArray();
  Independent.Cycle(g,b,result);return result;
 }
 int[] Extend(int[] h,int[] path) {
  while(h.Length<g.N){var next=old.Subgroups.First(k=>k.Length>h.Length&&old.Contained(h,k));path=old.Glue(next,h,path);h=next;}
  return path;
 }
 int[] OneHole(int hole){
  int z=g.All.FirstOrDefault(x=>g.Order(x)>=5);
  int[] h,path;
  if(z!=0){h=old.Cyclic(z);path=ThreeConstructor.OneCyclic(h.Length).Select(i=>g.Mul(z,i)).ToArray();}
  else{
   h=old.Subgroups.First(k=>k.Length==9);int d=h.First(x=>x!=0),e=h.First(x=>!old.Cyclic(d).Contains(x));
   path=new[]{1,3,4,7,2,6,8,5}.Select(i=>g.Add(g.Mul(d,i%3),g.Mul(e,i/3))).ToArray();
  }
  Independent.Cycle(g,h.Where(x=>x!=0).ToArray(),path);
  return Extend(h,path).Select(x=>g.Sum[x,hole]).ToArray();
 }
 int[] PlaneBase(int[] holes){
  var fixtures=new Dictionary<string,int[]>{
   ["0,1,2,3"]=new[]{4,5,6,7,8},["0,1,3,4"]=new[]{2,5,6,8,7},
   ["0,1,3,5"]=new[]{2,4,7,6,8},["0,1,3,7"]=new[]{2,4,5,6,8}};
  foreach(int a in holes)foreach(int b in holes.Where(x=>x!=a))foreach(int c in holes.Where(x=>x!=a&&x!=b)){
   int d=g.Sub(b,a),e=g.Sub(c,a);if(old.Cyclic(d).Contains(e))continue;
   int[] map=Enumerable.Range(0,9).Select(i=>g.Add(a,g.Mul(d,i%3),g.Mul(e,i/3))).ToArray();
   int[] normalized=holes.Select(x=>Array.IndexOf(map,x)).Order().ToArray();
   if(fixtures.TryGetValue(Key(normalized),out var witness))return witness.Select(i=>map[i]).ToArray();
  }
  throw new Exception("plane classification failed");
 }
 bool FullFiber(int[] h,int r,int[] holes){
  int q=g.N/h.Length;return Enumerable.Range(0,q).Any(i=>!holes.Any(d=>h.Contains(g.Sub(d,g.Mul(r,i)))));
 }
 int FiberMax(int[] h,int r,int[] holes){
  int q=g.N/h.Length;return Enumerable.Range(0,q).Max(i=>holes.Count(d=>h.Contains(g.Sub(d,g.Mul(r,i)))));
 }
 public int[] Build(int[] holes){
  string key=Key(holes);if(built.TryGetValue(key,out var cached))return cached;
  Check.Assert(holes.Length<=4&&g.N-holes.Length>=3,"construction domain");
  int[] ans;
  if(holes.Length==0){ans=old.Full(g.All,g.All.First(x=>x!=0));Branch="full";}
  else if(holes.Length==1){ans=OneHole(holes[0]);Branch="one";}
  else if(holes.Length==2){ans=old.TwoDeleted(g.All,holes[0],holes[1]);Branch="two";}
  else if(holes.Length==3){
   three??=new Complete(g);int a=holes[0];ans=three.Build(g.Sub(holes[1],a),g.Sub(holes[2],a)).Select(x=>g.Sum[x,a]).ToArray();Branch="three";
  }else{
   int generator=g.All.FirstOrDefault(x=>g.Order(x)==g.N);
   if(generator!=0){
    int[] indices=Enumerable.Range(0,g.N).Where(i=>!holes.Contains(g.Mul(generator,i))).ToArray();
    ans=OddCycle(indices).Select(i=>g.Mul(generator,i)).ToArray();Branch="cyclic-odd";CyclicCases++;
   }else if(g.N==9){ans=PlaneBase(holes);Branch="plane-nine";PlaneCases++;}
   else{
    int[]? h=null;int r=0;string kind="";
    if(g.N==25){
     foreach(var hh in old.Subgroups.Where(hh=>hh.Length==5)){int rr=g.All.First(x=>!hh.Contains(x));if(FiberMax(hh,rr,holes)<=2){h=hh;r=rr;break;}}
     kind="plane-five-direction";Check.Assert(h!=null,"direction avoiding collinear triples");
    }else{
     int p=Enumerable.Range(5,g.N-4).FirstOrDefault(x=>g.N%x==0&&Enumerable.Range(2,(int)Math.Sqrt(x)-1).All(d=>x%d!=0));
     if(p!=0){h=old.Subgroups.First(hh=>hh.Length==g.N/p);r=g.All.First(x=>!h.Contains(x));kind="prime-quotient";}
     else{
      foreach(var hh in old.Subgroups.Where(hh=>hh.Length==g.N/3)){int rr=g.All.First(x=>!hh.Contains(x));if(FullFiber(hh,rr,holes)){h=hh;r=rr;break;}}
      kind="three-quotient";Check.Assert(h!=null,"F3 functional selection");
     }
    }
    Check.Assert(h!=null&&h.Length>4,"kernel size");int anchor=holes[0];
    if(holes.All(x=>h!.Contains(g.Sub(x,anchor)))){
     int[] rel=holes.Select(x=>g.Sub(x,anchor)).ToArray();
     int[] path=LocalCycle(h!,h!.Except(rel).ToArray());
     ans=old.Glue(g.All,h!,path,r).Select(x=>g.Sum[x,anchor]).ToArray();
     Branch=kind+"-induction";Inductions++;
    }else{
     ans=glue.Build(h!,r,holes)??throw new Exception("proved gluing hypotheses missing");
     Branch=kind+"-glue";GlueCases++;
    }
   }
  }
  Independent.Cycle(g,g.All.Except(holes).ToArray(),ans);built[key]=ans;return ans;
 }
 public static void Run(int max=35){
  var watch=Stopwatch.StartNew();var rows=new List<object>();
  using var log=new StreamWriter($"construction-{max}.jsonl");
  using var w=new StreamWriter($"construction-witnesses-{max}.jsonl");
  foreach(var g in Program.Groups(max)){
   var maker=new FourConstructor(g);var counts=new Dictionary<string,int>();int count=0;
   for(int d=1;d<g.N;d++)for(int e=d+1;e<g.N;e++)for(int f=e+1;f<g.N;f++){
    int[] holes={0,d,e,f};var cycle=maker.Build(holes);count++;
    counts[maker.Branch]=counts.GetValueOrDefault(maker.Branch)+1;
    Program.Save(w,new{group=g.Name,dims=g.D,holes,cycle,missing=Check.Cycle(g,holes,cycle),branch=maker.Branch});
   }
   var row=new{group=g.Name,count,branches=counts,maker.CyclicCases,maker.PlaneCases,maker.Inductions,maker.GlueCases};
   rows.Add(row);Program.Save(log,row);Console.WriteLine(JsonSerializer.Serialize(row));
  }
  File.WriteAllText($"construction-summary-{max}.json",JsonSerializer.Serialize(new{completed=true,groups=rows,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
 }
 public static void CyclicTest(){
  var watch=Stopwatch.StartNew();long sets=0,edges=0,four=0;
  for(int n=3;n<=21;n++)for(int mask=0;mask<(1<<n);mask++){
   int k=System.Numerics.BitOperations.PopCount((uint)mask);if(k<3||k%2==0)continue;
   int[] a=Enumerable.Range(0,n).Where(i=>(mask&(1<<i))!=0).ToArray(),cycle=OddCycle(a);
   int[] sums=Enumerable.Range(0,k).Select(i=>cycle[i]+cycle[(i+1)%k]).ToArray();
   Check.Assert(sums.Distinct().Count()==k&&sums.Max()-sums.Min()<n&&sums.Select(x=>x%n).Distinct().Count()==k,"cyclic odd subset");
   Check.Assert(cycle.Order().SequenceEqual(a),"cyclic subset coverage");sets++;edges+=k;
  }
  for(int n=23;n<=101;n+=2)for(int b=1;b<n;b++)for(int c=b+1;c<n;c++)for(int d=c+1;d<n;d++){
   int[] a=Enumerable.Range(1,n-1).Where(x=>x!=b&&x!=c&&x!=d).ToArray(),cycle=OddCycle(a);
   int[] sums=Enumerable.Range(0,cycle.Length).Select(i=>cycle[i]+cycle[(i+1)%cycle.Length]).ToArray();
   Check.Assert(sums.Distinct().Count()==cycle.Length&&sums.Max()-sums.Min()<n,"cyclic four deletion");
   four++;
  }
  var result=new{completed=true,allOddSubsetsModuli3Through21=sets,edges,normalizedFourSetsOddOrders23Through101=four,seconds=watch.Elapsed.TotalSeconds};
  File.WriteAllText("cyclic-odd-summary.json",JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true}));Console.WriteLine(JsonSerializer.Serialize(result));
 }
}

