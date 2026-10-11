using System.Diagnostics;
using System.Text.Json;
// Three-deletion constructions with independent checking in Program.cs.
sealed class ThreeConstructor {
 internal readonly Group g;internal readonly Constructor old;
 public long Seams,Closures,FullPaths,Reversals,NonzeroQr;
 public ThreeConstructor(Group g){this.g=g;old=new Constructor(g);}
 public static int[] OneCyclic(int m){var r=new List<int>();int k=m/4;if(m%4==1){for(int i=2*k+2;i<=4*k;i+=2)r.Add(i);for(int i=2;i<=2*k;i+=2)r.Add(i);for(int i=2*k-1;i>=1;i-=2)r.Add(i);for(int i=4*k-1;i>=2*k+1;i-=2)r.Add(i);}else{for(int i=2*k+2;i<=4*k+2;i+=2)r.Add(i);for(int i=2;i<=2*k;i+=2)r.Add(i);for(int i=2*k+1;i>=1;i-=2)r.Add(i);for(int i=4*k+1;i>=2*k+3;i-=2)r.Add(i);}return r.ToArray();}
 // Any number >= 2 of nonzero summands. Reserve the last two for the target.
 internal int[] NonzeroSum(int[] h,int count,int target){Check.Assert(count>=2,"summand count");int z=h.First(x=>x!=0);var d=new List<int>();for(int i=0;i<count-2;i++){d.Add(z);target=g.Sub(target,z);}int a=h.First(x=>x!=0&&x!=target);d.Add(a);d.Add(g.Sub(target,a));return d.ToArray();}
 public int[] Extend(int[] h,int[] k,int[] path){while(h.Length<k.Length){int[] next=old.Subgroups.First(z=>z.Length>h.Length&&old.Contained(h,z)&&old.Contained(z,k));path=old.Glue(next,h,path);h=next;}return path;}
 public int[] TwoFibers(int d,int r,int cut=0,bool reverse0=false,bool reverse1=false){int[] h=old.Cyclic(d);int m=h.Length;Check.Assert(m>=5&&!h.Contains(r),"two-fiber hypotheses");int[] k=old.Subgroups.First(z=>old.Contained(h,z)&&z.Contains(r));int q=k.Length/m;
  int[] p0=Enumerable.Range(2,m-2).Select(i=>g.Mul(d,i)).ToArray();if(reverse0)Array.Reverse(p0);p0=Enumerable.Range(0,p0.Length).Select(i=>p0[(i+cut)%p0.Length]).ToArray();int u=p0[0],v=p0[^1];int[] one=OneCyclic(m).Select(i=>g.Mul(d,i)).ToArray();Check.Assert(!one.Contains(0),"one-hole excludes zero");Independent.Cycle(g,h.Where(x=>x!=0).ToArray(),one);
  int pos=Array.IndexOf(one,v);Check.Assert(pos>=0,"shared endpoint allowed");int sign=reverse1?-1:1;int[] p1=Enumerable.Range(0,m-1).Select(i=>g.Add(r,one[(pos+sign*i+(m-1))%(m-1)])).ToArray();int w=g.Sub(p1[^1],r);
  // At index three, exactly one orientation can force coincident full endpoints.
  if(q==3&&g.Add(w,g.Mul(r,3))==u){sign=-sign;p1=Enumerable.Range(0,m-1).Select(i=>g.Add(r,one[(pos+sign*i+(m-1))%(m-1)])).ToArray();w=g.Sub(p1[^1],r);Reversals++;}
  int[] delta=new int[q];delta[0]=g.Sub(v,u);delta[1]=g.Sub(w,v);int target=g.Neg[g.Add(g.Mul(r,q),delta[0],delta[1])];if(q==3){Check.Assert(target!=0,"index-three correction nonzero");delta[2]=target;}else Array.Copy(NonzeroSum(h,q-2,target),0,delta,2,q-2);
  int[] x=new int[q+1],y=new int[q];x[0]=u;for(int i=0;i<q;i++){y[i]=g.Sum[x[i],delta[i]];x[i+1]=g.Sum[y[i],r];}Check.Assert(x[q]==x[0],"closure");Closures++;if(g.Mul(r,q)!=0)NonzeroQr++;
  var blocks=new int[q][];blocks[0]=p0;blocks[1]=p1;Check.Assert(x[1]==p1[0]&&y[1]==p1[^1],"fixed second endpoints");for(int i=2;i<q;i++){var hc=old.Full(h,delta[i]);blocks[i]=new[]{x[i]}.Concat(hc.Skip(1).Reverse().Select(t=>g.Sum[x[i],t])).ToArray();var internalSums=Enumerable.Range(0,m-1).Select(j=>Check.Add(g.D,blocks[i][j],blocks[i][j+1])).ToArray();var expected=h.Select(t=>Check.Add(g.D,g.Mul(x[i],2),t)).Except(new[]{Check.Add(g.D,x[i],y[i])}).Order();Check.Assert(internalSums.Distinct().Count()==m-1&&internalSums.Order().SequenceEqual(expected),"full block exact colors");FullPaths++;}
  for(int i=0;i<q;i++){Check.Assert(Check.Add(g.D,y[i],x[(i+2)%q])==Check.Add(g.D,x[(i+1)%q],y[(i+1)%q]),"seam identity");Seams++;}
  int[] cycle=Enumerable.Range(0,q).SelectMany(i=>blocks[2*i%q]).ToArray();Independent.Cycle(g,k.Except(new[]{0,d,r}).ToArray(),cycle);
  var expectedMissing=new[]{g.Neg[d],g.Mul(d,3),g.Mul(r,2)}.Order();var actual=k.Except(Enumerable.Range(0,cycle.Length).Select(i=>Check.Add(g.D,cycle[i],cycle[(i+1)%cycle.Length]))).Order();Check.Assert(actual.SequenceEqual(expectedMissing),"three exact omitted colors");
  cycle=Extend(k,g.All,cycle);Check.Assert(Check.Cycle(g,new[]{0,d,r},cycle).Order().SequenceEqual(expectedMissing),"extended missing colors");return cycle;
 }
 public int[] ElementaryBase(int d,int e){Check.Assert(g.Order(d)==3&&g.Order(e)==3&&!old.Cyclic(d).Contains(e),"elementary plane");int[] code={2,4,5,7,6,8};int[] path=code.Select(i=>g.Add(g.Mul(d,i%3),g.Mul(e,i/3))).ToArray();int[] h=old.Subgroups.First(z=>z.Contains(d)&&z.Contains(e));Independent.Cycle(g,h.Except(new[]{0,d,e}).ToArray(),path);return Extend(h,g.All,path);}
}
static class Structure {
 public static void Run(){var total=Stopwatch.StartNew();using var log=new StreamWriter("structure.jsonl");using var witnesses=new StreamWriter("structural-witnesses.jsonl");for(int m=5;m<=1001;m+=2){var g=new Group(m);var path=ThreeConstructor.OneCyclic(m);Check.Assert(Check.Cycle(g,new[]{0},path).SequenceEqual(new[]{0}),"classical one-deletion formula");}
  foreach(var g in Program.Groups()){var sw=Stopwatch.StartNew();var maker=new ThreeConstructor(g);long cases=0,planes=0,normalizedCovered=0;for(int d=1;d<g.N;d++)for(int e=d+1;e<g.N;e++){int[]? chosen=null;foreach(var (a,b,c) in new[]{(0,d,e),(d,0,e),(0,e,d),(e,0,d),(d,e,0),(e,d,0)}){int dd=g.Sub(b,a),rr=g.Sub(c,a);int[] cyclic=Enumerable.Range(0,g.Order(dd)).Select(i=>g.Mul(dd,i)).ToArray();if(cyclic.Contains(rr))continue;if(cyclic.Length>=5){for(int cut=0;cut<cyclic.Length-2;cut++)for(int orientation=0;orientation<4;orientation++){var p=maker.TwoFibers(dd,rr,cut,(orientation&1)!=0,(orientation&2)!=0).Select(x=>g.Sum[x,a]).ToArray();Check.Cycle(g,new[]{0,d,e},p);chosen??=p;cases++;}}else if(g.Order(rr)==3){var p=maker.ElementaryBase(dd,rr).Select(x=>g.Sum[x,a]).ToArray();Check.Cycle(g,new[]{0,d,e},p);chosen??=p;planes++;}}
   if(chosen!=null){normalizedCovered++;Program.Save(witnesses,new{group=g.Name,holes=new[]{0,d,e},cycle=chosen,missing=Check.Cycle(g,new[]{0,d,e},chosen)});}}
   var row=new{group=g.Name,cases,planes,normalizedCovered,maker.Seams,maker.Closures,maker.FullPaths,maker.Reversals,maker.NonzeroQr,failures=0,seconds=sw.Elapsed.TotalSeconds};Program.Save(log,row);Console.WriteLine(JsonSerializer.Serialize(row));}
  File.WriteAllText("structure-summary.json",JsonSerializer.Serialize(new{completed=true,oneDeletionCyclicOrdersTested=499,seconds=total.Elapsed.TotalSeconds,failures=0}));}
}
