using System.Diagnostics;
using System.Text.Json;

sealed class GeneralGlue {
 readonly Group g;readonly Constructor old;readonly Search? search;
 readonly Func<int[],int[],int[]>? localFactory;
 readonly Dictionary<string,int[]> local=new();readonly Random rng=new(4004);
 public long Trials,BadStarts,Repairs,Seams,NonzeroQr,Colors;
 public GeneralGlue(Group g,Func<int[],int[],int[]>? localFactory=null){this.g=g;old=new Constructor(g);this.localFactory=localFactory;search=localFactory==null?new Search(g):null;}
 public Constructor Old=>old;
 int[] Cycle(int[] h,int[] b) {
  string key=string.Join(",",b.Order());
  if(local.TryGetValue(key,out var c))return c;
  if(b.Length==h.Length)c=old.Full(h,h.First(x=>x!=0));
  else if(localFactory!=null)c=localFactory(h,b);
  else {var result=search!.Solve(g.All.Except(b).ToArray(),limit:100000,tries:100);
   Check.Assert(result.cycle!=null,"local cycle not found: "+key);c=result.cycle!;}
  Independent.Cycle(g,b,c);local[key]=c;return c;
 }
 static int[] Cut(int[] cycle,int start,bool reverse){
  int pos=Array.IndexOf(cycle,start);Check.Assert(pos>=0,"start outside cycle");
  return Enumerable.Range(0,cycle.Length).Select(j=>cycle[(pos+(reverse?-j:j)+cycle.Length)%cycle.Length]).ToArray();
 }
 public int[]? Build(int[] h,int r,int[] holes) {
  int q=g.N/h.Length;Check.Assert(old.QuotientOrder(r,h)==q,"quotient cyclic");
  if(h.Length<=holes.Length)return null;
  int full=-1;
  for(int i=0;i<q;i++)if(!holes.Any(x=>h.Contains(g.Sub(x,g.Mul(r,i))))){full=i;break;}
  if(full<0)return null;
  int t=g.Mul(r,(full+1)%q);
  int[][] cycles=new int[q-1][];int[][] bs=new int[q][];
  int[] offsets=Enumerable.Range(0,q).Select(i=>g.Add(t,g.Mul(r,i))).ToArray();
  for(int i=0;i<q;i++){
   bs[i]=h.Where(z=>!holes.Contains(g.Sum[offsets[i],z])).ToArray();
   if(bs[i].Length<3)return null;
   if(i<q-1){cycles[i]=(int[])Cycle(h,bs[i]).Clone();if(rng.Next(2)==0)Array.Reverse(cycles[i]);}
  }
  Check.Assert(bs[^1].Length==h.Length,"last fiber full");
  int[][] paths=new int[q][];int first=-1;int bad=0;
  foreach(int u in h) {
   int z=u;bool valid=true;
   for(int i=0;i<q-1;i++){
    int pos=Array.IndexOf(cycles[i],z);if(pos<0){valid=false;break;}
    z=cycles[i][(pos+cycles[i].Length-1)%cycles[i].Length];
   }
   if(valid){if(first<0)first=u;}else bad++;
  }
  Check.Assert(bad<=holes.Length&&first>=0,"forbidden-start union bound");BadStarts+=bad;
  int next=first,qr=g.Mul(r,q),target=g.Sub(first,qr);
  if(qr!=0)NonzeroQr++;
  for(int i=0;i<q-1;i++){
   paths[i]=Cut(cycles[i],next,false);
   if(i==q-2&&paths[i][^1]==target){paths[i]=Cut(cycles[i],next,true);Repairs++;}
   next=paths[i][^1];
  }
  Check.Assert(next!=target,"orientation avoidance");int delta=g.Sub(target,next);
  var fullCycle=old.Full(h,delta);
  paths[q-1]=new[]{next}.Concat(fullCycle.Skip(1).Reverse().Select(x=>g.Sum[next,x])).ToArray();
  var expected=new HashSet<int>();
  for(int i=0;i<q;i++){
   paths[i]=paths[i].Select(x=>g.Sum[offsets[i],x]).ToArray();
   if(i==q-1)foreach(int x in h)Check.Assert(expected.Add(Check.Add(g.D,g.Mul(offsets[i],2),x)),"coset overlap");
   else for(int j=0;j<cycles[i].Length;j++){
    int color=Check.Add(g.D,g.Mul(offsets[i],2),Check.Add(g.D,cycles[i][j],cycles[i][(j+1)%cycles[i].Length]));
    Check.Assert(expected.Add(color),"local color overlap");
   }
  }
  for(int i=0;i<q;i++){
   int j=(i+1)%q,k=(i+2)%q;
   Check.Assert(Check.Add(g.D,paths[i][^1],r)==paths[j][0],"endpoint recurrence");
   Check.Assert(Check.Add(g.D,paths[i][^1],paths[k][0])==Check.Add(g.D,paths[j][0],paths[j][^1]),"seam including wrap");Seams++;
  }
  int[] result=Enumerable.Range(0,q).SelectMany(i=>paths[2*i%q]).ToArray();
  Check.Cycle(g,holes,result);
  var actual=Enumerable.Range(0,result.Length).Select(i=>Check.Add(g.D,result[i],result[(i+1)%result.Length])).ToHashSet();
  Check.Assert(actual.SetEquals(expected),"preserved local color sets");Colors+=actual.Count;Trials++;
  return result;
 }
 public static void Run(int max=35) {
  var watch=Stopwatch.StartNew();var rows=new List<object>();
  using var log=new StreamWriter("general-glue.jsonl");using var w=new StreamWriter("general-glue-witnesses.jsonl");
  foreach(var g in Program.Groups(max)){
   var maker=new GeneralGlue(g);long eligible=0,skipped=0;
   foreach(var h in maker.old.Subgroups.Where(h=>h.Length>4&&h.Length<g.N)){
    int q=g.N/h.Length;
    foreach(int r in g.All.Where(r=>maker.old.QuotientOrder(r,h)==q))
     for(int d=1;d<g.N;d++)for(int e=d+1;e<g.N;e++)for(int f=e+1;f<g.N;f++){
      int[] holes={0,d,e,f};var cycle=maker.Build(h,r,holes);
      if(cycle==null){skipped++;continue;}eligible++;
      if(eligible<=5)Program.Save(w,new{group=g.Name,dims=g.D,h,r,holes,cycle,missing=Check.Cycle(g,holes,cycle)});
     }
   }
   var row=new{group=g.Name,eligible,skipped,maker.Trials,maker.BadStarts,maker.Repairs,maker.Seams,maker.NonzeroQr,maker.Colors};
   rows.Add(row);Program.Save(log,row);Console.WriteLine(JsonSerializer.Serialize(row));
  }
  File.WriteAllText("general-glue-summary.json",JsonSerializer.Serialize(new{completed=true,groups=rows,seconds=watch.Elapsed.TotalSeconds},new JsonSerializerOptions{WriteIndented=true}));
 }
}

