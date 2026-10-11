using System.Diagnostics;
using System.Text.Json;
sealed class Constructor {
 readonly Group g; public readonly List<int[]> Subgroups;readonly Dictionary<string,int[]> fullCache=new();
 public long GlueCalls,EndpointChecks,JoinChecks,InternalChecks;
 public Constructor(Group g){this.g=g;Subgroups=GetSubgroups(g);}
 static string Key(int[] a)=>string.Join(",",a);
 static List<int[]> GetSubgroups(Group g){var dict=new Dictionary<string,int[]>();var queue=new Queue<int[]>();int[] z={0};dict.Add("0",z);queue.Enqueue(z);while(queue.Count>0){var h=queue.Dequeue();foreach(int x in g.All)if(!h.Contains(x)){var v=new HashSet<int>();int y=0;do{foreach(int a in h)v.Add(g.Sum[a,y]);y=g.Sum[y,x];}while(y!=0);var s=v.Order().ToArray();if(dict.TryAdd(Key(s),s))queue.Enqueue(s);}}return dict.Values.OrderBy(h=>h.Length).ThenBy(Key).ToList();}
 public bool Contained(int[] h,int[] k)=>h.All(k.Contains);
 public int[] Cyclic(int d){var h=new List<int>();int x=0;do{h.Add(x);x=g.Sum[x,d];}while(x!=0);return h.Order().ToArray();}
 static bool Prime(int n)=>n>=2&&!Enumerable.Range(2,Math.Max(0,(int)Math.Sqrt(n)-1)).Any(d=>n%d==0);
 public int QuotientOrder(int r,int[] h){int t=r,q=1;while(!h.Contains(t)){t=g.Sum[t,r];q++;}return q;}
 // Returns a cycle on k beginning 0,d. Strong induction on |k|.
 public int[] Full(int[] k,int d){Independent.Assert(d!=0&&k.Contains(d),"full edge input");string key=Key(k)+":"+d;if(fullCache.TryGetValue(key,out var cached))return cached;
  int[] ans;
  if(Prime(k.Length)){ans=Enumerable.Range(0,k.Length).Select(i=>g.Mul(d,i)).ToArray();}
  else{
   int[] h=Subgroups.Where(h=>h.Length<k.Length&&Contained(h,k)).MaxBy(h=>h.Length)!;int q=k.Length/h.Length;Independent.Assert(Prime(q)&&h.Length>=3,"maximal subgroup index");
   if(!h.Contains(d)){
    int[] hc=Full(h,h.First(x=>x!=0));ans=hc.SelectMany(x=>Enumerable.Range(0,q).Select(i=>g.Add(x,g.Mul(d,i)))).ToArray();
   }else{
    int[] hc=Full(h,d);ans=Glue(k,h,hc);
   }
  }
  Independent.Cycle(g,k,ans);Independent.Assert(ans[0]==0&&ans[1]==d,"prescribed edge lost");fullCache.Add(key,ans);return ans;
 }
 public int[] TwoDeleted(int[] k,int a,int b){Independent.Assert(a!=b&&k.Contains(a)&&k.Contains(b)&&k.Length>=5,"two holes input");int d=g.Sub(b,a);int[] h=Cyclic(d);int m=h.Length;int[] path=m==3?new[]{g.Mul(d,2)}:Enumerable.Range(2,m-2).Select(i=>g.Mul(d,i)).ToArray();
  if(path.Length>=3)Independent.Cycle(g,h.Where(x=>x!=0&&x!=d).ToArray(),path);
  while(h.Length<k.Length){int[] next=Subgroups.First(z=>z.Length>h.Length&&Contained(h,z)&&Contained(z,k));Independent.Assert(Prime(next.Length/h.Length),"chain index");path=Glue(next,h,path);h=next;}
  int[] result=path.Select(x=>g.Sum[x,a]).ToArray();Independent.Cycle(g,k.Where(x=>x!=a&&x!=b).ToArray(),result);return result;
 }
 // Cyclic-quotient gluing. bPath is either a rainbow cycle (cut at its closing edge)
 // or a singleton. All full coset paths are constructed recursively, not searched.
 public int[] Glue(int[] k,int[] h,int[] bPath,int? representative=null){int q=k.Length/h.Length;Independent.Assert(q>=3&&q%2==1&&h.Length>=3,"glue size");Independent.Assert(bPath.Length==1||bPath.Length>=3,"bad fiber size");Independent.Assert(bPath.All(h.Contains)&&bPath.Distinct().Count()==bPath.Length,"bad fiber vertices");if(bPath.Length>=3)Independent.Cycle(g,bPath,bPath);
  int r=representative??k.First(x=>QuotientOrder(x,h)==q);Independent.Assert(k.Contains(r)&&QuotientOrder(r,h)==q,"quotient generator");int[] delta=new int[q];delta[0]=g.Sub(bPath[^1],bPath[0]);int target=g.Neg[g.Add(g.Mul(r,q),delta[0])];int a=h.First(x=>x!=0&&x!=target);delta[1]=a;delta[2]=g.Sub(target,a);int c=h.First(x=>x!=0);for(int i=3;i<q;i+=2){delta[i]=c;delta[i+1]=g.Neg[c];}
  int[] start=new int[q+1],end=new int[q];start[0]=bPath[0];for(int i=0;i<q;i++){end[i]=g.Sum[start[i],delta[i]];start[i+1]=g.Sum[end[i],r];}Independent.Assert(start[q]==start[0],"endpoint telescoping");Independent.Assert(end[0]==bPath[^1],"special endpoint");EndpointChecks++;
  int[][] blocks=new int[q][];blocks[0]=(int[])bPath.Clone();for(int i=1;i<q;i++){Independent.Assert(delta[i]!=0,"zero full-fiber difference");int[] hc=Full(h,delta[i]);blocks[i]=new[]{start[i]}.Concat(hc.Skip(1).Reverse().Select(x=>g.Sum[start[i],x])).ToArray();Independent.Assert(blocks[i][0]==start[i]&&blocks[i][^1]==end[i],"block endpoints");
   var expected=h.Select(x=>Independent.Add(g.D,g.Mul(start[i],2),x)).ToHashSet();int omitted=Independent.Add(g.D,start[i],end[i]);expected.Remove(omitted);var actual=new HashSet<int>();for(int j=0;j<blocks[i].Length-1;j++)Independent.Assert(actual.Add(Independent.Add(g.D,blocks[i][j],blocks[i][j+1])),"block sum duplicate");Independent.Assert(actual.SetEquals(expected),"block missing-color set");InternalChecks++;
  }
  for(int i=0;i<q;i++){int join=Independent.Add(g.D,blocks[i][^1],blocks[(i+2)%q][0]);int holeColor=Independent.Add(g.D,blocks[(i+1)%q][0],blocks[(i+1)%q][^1]);Independent.Assert(join==holeColor,"joining identity");JoinChecks++;}
  int[] cycle=Enumerable.Range(0,q).SelectMany(j=>blocks[(2*j)%q]).ToArray();int[] subset=k.Where(x=>!h.Contains(x)||bPath.Contains(x)).ToArray();Independent.Cycle(g,subset,cycle);GlueCalls++;return cycle;
 }
}

