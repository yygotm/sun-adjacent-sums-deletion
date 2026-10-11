using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text.Json;

// Independent implementation for Sun, Conjecture 3.3(i).
sealed class Group
{
    public readonly int[] D;
    public readonly int N;
    public readonly ulong Full;
    public readonly string Name;
    public readonly int[,] Sum;
    public readonly int[] Neg;
    readonly ulong[][] trans;
    public Group(params int[] d)
    {
        D=d; N=d.Aggregate(1,(a,b)=>a*b); if(N<3 || N>35 || N%2==0) throw new ArgumentException("Supported odd orders: 3..35"); Full=(1UL<<N)-1;
        Name=string.Join("x",d.Select(x=>"Z"+x));
        Sum=new int[N,N]; Neg=new int[N];
        for(int a=0;a<N;a++) for(int b=0;b<N;b++) Sum[a,b]=Add(a,b);
        for(int a=0;a<N;a++) for(int b=0;b<N;b++) if(Sum[a,b]==0) Neg[a]=b;
        trans=new ulong[N][];
        for(int delta=0;delta<N;delta++)
        {
            var t=trans[delta]=new ulong[8*256];
            for(int block=0;block<8;block++) for(int x=1;x<256;x++)
            {
                int bit=BitOperations.TrailingZeroCount((ulong)x), elem=block*8+bit;
                t[block*256+x]=t[block*256+(x&(x-1))] | (elem<N?1UL<<Sum[elem,delta]:0);
            }
        }
    }
    int Add(int a,int b)
    {
        int ans=0,stride=1;
        foreach(int d in D) { ans+=((a%d+b%d)%d)*stride; a/=d; b/=d; stride*=d; }
        return ans;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ulong Translate(ulong mask,int delta)
    {
        if(D.Length==1) return ((mask<<delta)|(mask>>(N-delta)))&Full;
        var t=trans[delta];
        return t[mask&255] | t[256+((mask>>8)&255)] | t[512+((mask>>16)&255)] | t[768+((mask>>24)&255)] | t[1024+((mask>>32)&255)] | t[1280+((mask>>40)&255)] | t[1536+((mask>>48)&255)] | t[1792+(mask>>56)];
    }
    public int StabilizerIfCanonical(ulong mask)
    {
        int stabilizer=1;
        for(ulong r=mask&~1UL;r!=0;r&=r-1)
        {
            int a=BitOperations.TrailingZeroCount(r);
            ulong other=Translate(mask,Neg[a]);
            if(other<mask) return 0;
            if(other==mask) stabilizer++;
        }
        return stabilizer;
    }
}

// Deliberately separate from the search's addition table, bit translations,
// candidate generation, and cached masks. Reconstruct coordinates and sums.
static class WitnessVerifier
{
    public static bool Check(int[] radices,ulong subset,int[] cycle,int length)
    {
        int order=1; foreach(int d in radices) order*=d;
        var expected=new HashSet<int>();
        for(int i=0;i<order;i++) if((subset&(1UL<<i))!=0) expected.Add(i);
        if(length!=expected.Count || length<3 || cycle.Length<length) return false;
        var actual=new HashSet<int>(); var sums=new HashSet<int>();
        for(int i=0;i<length;i++)
        {
            int a=cycle[i],b=cycle[(i+1)%length];
            if(a<0||a>=order||b<0||b>=order||!actual.Add(a)) return false;
            int s=0,place=1;
            for(int k=0;k<radices.Length;k++)
            {
                int x=(a/place)%radices[k],y=(b/place)%radices[k];
                s+=((x+y)%radices[k])*place; place*=radices[k];
            }
            if(!sums.Add(s)) return false;
        }
        return actual.SetEquals(expected) && sums.Count==length;
    }
}

sealed class Solver
{
    readonly Group g;
    public readonly int[] Path=new int[64];
    readonly int[] order=new int[64];
    long budget,nodes;
    int size;
    bool stopped;
    ulong rng;
    public long Nodes;
    
    public Solver(Group group) { g=group; }
    ulong Rand() { rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
    // Return 1=witness, 0=exhaustive failure, -1=budget exhausted.
    public int Solve(ulong mask,long limit=5000,int attempt=0)
    {
        size=BitOperations.PopCount(mask); int k=0;
        for(ulong r=mask;r!=0;r&=r-1) order[k++]=BitOperations.TrailingZeroCount(r);
        rng=((ulong)mask<<32) ^ ((ulong)(attempt+1)*0x9e3779b97f4a7c15UL);
        if(attempt!=0)
            for(int i=size-1;i>1;i--) { int j=1+(int)(Rand()%(ulong)i); (order[i],order[j])=(order[j],order[i]); }
        // The first branch is an induced ordering; accept only if its sums work.
        ulong used=0; bool good=true;
        for(int i=0;i<size;i++)
        {
            ulong b=1UL<<g.Sum[order[i],order[(i+1)%size]];
            if((used&b)!=0) { good=false; break; } used|=b;
        }
        if(good) { Array.Copy(order,Path,size); return 1; }
        budget=limit; nodes=0; stopped=false; Path[0]=0;
        bool ok=DFS(0,mask&~1UL,0,1);
        Nodes+=nodes;
        return ok?1:stopped?-1:0;
    }
    bool DFS(int last,ulong remaining,ulong used,int depth)
    {
        if(++nodes>budget) { stopped=true; return false; }
        if(remaining==0) return (used&(1UL<<last))==0;
        // One remaining vertex: test the two closing edges directly.
        if((remaining&(remaining-1))==0)
        {
            int v=BitOperations.TrailingZeroCount(remaining);
            ulong b=1UL<<g.Sum[last,v],c=1UL<<v;
            if(b==c || (used&(b|c))!=0) return false;
            Path[depth]=v; return true;
        }
        ulong candidates=remaining & g.Translate(g.Full^used,g.Neg[last]);
        // At least one unused vertex must be able to provide the closing sum.
        if((remaining & ~used)==0) return false;
        for(int i=1;i<size;i++)
        {
            int v=order[i]; ulong vb=1UL<<v;
            if((candidates&vb)==0) continue;
            Path[depth]=v;
            if(DFS(v,remaining^vb,used|(1UL<<g.Sum[last,v]),depth+1)) return true;
            if(stopped) return false;
        }
        return false;
    }
}

sealed class Block
{
    public int Id {get;set;}
    public long Start {get;set;}
    public long End {get;set;}
    public long Candidates {get;set;}
    public long Representatives {get;set;}
    public long NormalizedCovered {get;set;}
    public long AllCovered {get;set;}
    public long[] BySize {get;set;}=new long[64];
    public long[] NormalizedBySize {get;set;}=new long[64];
    public long[] AllBySize {get;set;}=new long[64];
    public long Nodes {get;set;}
    public long Retried {get;set;}
    public List<ulong> Counterexamples {get;set;}=new();
    public List<ulong> Unresolved {get;set;}=new();
    public double Seconds {get;set;}
    public string WitnessHash {get;set;}="";
}

static class Program
{
    static readonly JsonSerializerOptions Pretty=new(){WriteIndented=true};
    static readonly object Gate=new();
    
    static readonly int[][] Specs=Enumerable.Range(1,13).Select(k=>new[]{2*k+1})
        .Concat(new[]{new[]{3,3},new[]{5,5},new[]{3,9},new[]{3,3,3}}).OrderBy(d=>d.Aggregate(1,(a,b)=>a*b)).ToArray();
    static int Main(string[] args)
    {
        try
        {
            if(args.Contains("--selftest")) { SelfTest(); return 0; }
            string names=Value(args,"--groups","all"); int threads=int.Parse(Value(args,"--threads","8"));
            var groups=names=="all"?Specs.Select(d=>new Group(d)):names.Split(',').Select(s=>new Group(s.Split('x').Select(t=>int.Parse(t.TrimStart('Z'))).ToArray()));
            int chunk=int.Parse(Value(args,"--chunk-size","1048576")); string root=Value(args,"--output-root","runs"); if(chunk<1) throw new ArgumentException("Invalid chunk size"); foreach(var g in groups) Run(g,threads,chunk,root);
            return 0;
        }
        catch(Exception e) { Console.Error.WriteLine(e); return 1; }
    }
    static string Value(string[] a,string key,string fallback) { int i=Array.IndexOf(a,key); return i>=0?a[i+1]:fallback; }
    static long Choose(int n,int k) { long r=1; for(int j=1;j<=k;j++) r=r*(n-j+1)/j; return r; }
    static void Run(Group g,int threads,int Chunk,string root)
    {
        long half=1L<<(g.N-1); int count=(int)((half+Chunk-1)/Chunk);
        string dir=Path.Combine(root,g.Name); Directory.CreateDirectory(dir);
        string journal=Path.Combine(dir,"blocks.jsonl");
        var finished=new Dictionary<int,Block>();
        if(File.Exists(journal))
        {
            foreach(string line in File.ReadLines(journal))
            {
                if(string.IsNullOrWhiteSpace(line)) continue;
                var b=JsonSerializer.Deserialize<Block>(line)??throw new Exception("Invalid journal");
                if(!finished.TryAdd(b.Id,b)) throw new Exception("Duplicate block in journal");
            }
        }
        var wall=Stopwatch.StartNew();
        using var log=new StreamWriter(journal,true){AutoFlush=true};
        Parallel.For(0,count,new ParallelOptions{MaxDegreeOfParallelism=threads},id=>
        {
            lock(Gate) if(finished.ContainsKey(id)) return;
            var sw=Stopwatch.StartNew(); var solver=new Solver(g); var b=new Block{Id=id,Start=(long)id*Chunk,End=Math.Min(half,(long)(id+1)*Chunk)};
            ulong hash=14695981039346656037UL;
            for(long raw=b.Start;raw<b.End;raw++)
            {
                ulong mask=(ulong)(raw*2+1); int size=BitOperations.PopCount(mask); if(size<3) continue;
                b.Candidates++;
                int stab=g.StabilizerIfCanonical(mask); if(stab==0) continue;
                b.Representatives++; b.NormalizedCovered+=size/stab; b.AllCovered+=g.N/stab;
                b.BySize[size]++; b.NormalizedBySize[size]+=size/stab; b.AllBySize[size]+=g.N/stab;
                int result=solver.Solve(mask);
                if(result==-1)
                {
                    b.Retried++;
                    for(int attempt=1;attempt<=8 && result==-1;attempt++) result=solver.Solve(mask,attempt<=4?20000:200000,attempt);
                }
                if(result==1)
                {
                    if(!WitnessVerifier.Check(g.D,mask,solver.Path,size)) throw new Exception($"INVALID WITNESS {g.Name} {mask}");
                    hash=(hash^mask)*1099511628211UL;
                    for(int j=0;j<size;j++) hash=(hash^(ulong)solver.Path[j])*1099511628211UL;
                }
                else if(result==0) b.Counterexamples.Add(mask);
                else b.Unresolved.Add(mask);
            }
            b.Nodes=solver.Nodes; b.Seconds=sw.Elapsed.TotalSeconds; b.WitnessHash=hash.ToString("x16");
            lock(Gate)
            {
                log.WriteLine(JsonSerializer.Serialize(b)); finished.Add(id,b);
                if(finished.Count%8==0 || finished.Count==count)
                {
                    var progress=new{group=g.Name,completedBlocks=finished.Count,totalBlocks=count,elapsedSeconds=wall.Elapsed.TotalSeconds,
                        representatives=finished.Values.Sum(x=>x.Representatives),counterexamples=finished.Values.Sum(x=>x.Counterexamples.Count),unresolved=finished.Values.Sum(x=>x.Unresolved.Count)};
                    File.WriteAllText(Path.Combine(dir,"progress.json"),JsonSerializer.Serialize(progress,Pretty));
                    Console.WriteLine(JsonSerializer.Serialize(progress));
                }
            }
        });
        if(finished.Count!=count) throw new Exception("Incomplete block coverage");
        long normalized=finished.Values.Sum(b=>b.NormalizedCovered),all=finished.Values.Sum(b=>b.AllCovered);
        long expectedNormalized=half-g.N,expectedAll=(1L<<g.N)-1-g.N-(long)g.N*(g.N-1)/2;
        if(finished.Values.Sum(b=>b.Candidates)!=expectedNormalized || normalized!=expectedNormalized || all!=expectedAll) throw new Exception("COVERAGE MISMATCH");
        var bySize=new List<object>();
        for(int k=3;k<=g.N;k++)
        {
            long nc=finished.Values.Sum(b=>b.NormalizedBySize[k]),ac=finished.Values.Sum(b=>b.AllBySize[k]);
            if(nc!=Choose(g.N-1,k-1)||ac!=Choose(g.N,k)) throw new Exception("SIZE COVERAGE MISMATCH");
            bySize.Add(new{size=k,representatives=finished.Values.Sum(b=>b.BySize[k]),normalized=nc,all=ac});
        }
        var resultSummary=new{group=g.Name,radices=g.D,order=g.N,chunkSize=Chunk,maskBits=64,normalizedSubsets=normalized,allSubsets=all,
            representatives=finished.Values.Sum(b=>b.Representatives),counterexampleRepresentatives=finished.Values.SelectMany(b=>b.Counterexamples).ToArray(),
            unresolvedRepresentatives=finished.Values.SelectMany(b=>b.Unresolved).ToArray(),
            wallSecondsThisInvocation=wall.Elapsed.TotalSeconds,blockWorkerSeconds=finished.Values.Sum(b=>b.Seconds),
            searchNodes=finished.Values.Sum(b=>b.Nodes),retriedRepresentatives=finished.Values.Sum(b=>b.Retried),threads,
            coverageVerified=true,independentWitnessVerification=true,bySize};
        File.WriteAllText(Path.Combine(dir,"summary.json"),JsonSerializer.Serialize(resultSummary,Pretty));
        Console.WriteLine($"DONE {g.Name} representatives={finished.Values.Sum(b=>b.Representatives)} normalized={normalized} all={all} counterexamples={finished.Values.Sum(b=>b.Counterexamples.Count)} unresolved={finished.Values.Sum(b=>b.Unresolved.Count)} seconds={wall.Elapsed.TotalSeconds:F3}");
    }
    static void SelfTest()
    {
        long bruteSubsets=0;
        foreach(var d in Specs.Concat(new[]{new[]{29},new[]{31},new[]{33},new[]{35}}))
        {
            var g=new Group(d);
            // Validate every one-point translation and the optimized bit maps.
            for(int a=0;a<g.N;a++) for(int delta=0;delta<g.N;delta++)
            {
                int actual=0,p=1;
                foreach(int r in d) { actual+=(((a/p)%r+(delta/p)%r)%r)*p; p*=r; }
                if(g.Translate(1UL<<a,delta)!=(1UL<<actual)) throw new Exception("Translation mismatch");
            }
            var solver=new Solver(g);
            int res=solver.Solve(g.Full,1000000);
            if(res!=1 || !WitnessVerifier.Check(d,g.Full,solver.Path,g.N)) throw new Exception("Full-group test failed");
            if(WitnessVerifier.Check(d,g.Full,solver.Path,g.N-1)) throw new Exception("Verifier accepted bad length");
            int saved=solver.Path[1]; solver.Path[1]=solver.Path[0];
            if(WitnessVerifier.Check(d,g.Full,solver.Path,g.N)) throw new Exception("Verifier accepted duplicate");
            solver.Path[1]=saved;
            if(g.N<=9)
            {
                for(ulong m=1;m<=g.Full;m+=2)
                {
                    int n=BitOperations.PopCount(m); if(n<3) continue;
                    var elems=Enumerable.Range(0,g.N).Where(a=>(m&(1UL<<a))!=0).ToArray();
                    bool brute=Permute(elems,1,d,m);
                    int result=solver.Solve(m,10000000);
                    if(result<0 || brute!=(result==1) || (result==1&&!WitnessVerifier.Check(d,m,solver.Path,n))) throw new Exception("Brute-force disagreement");
                    bruteSubsets++;
                }
            }
        }
        string msg=$"PASS: singleton translations for every target group and Z29/Z31/Z33/Z35; full-group witnesses; verifier negative tests; independent permutation enumeration on {bruteSubsets} normalized subsets in all groups of order <=9.";
        File.WriteAllText("selftest.txt",msg+Environment.NewLine); Console.WriteLine(msg);
    }
    static bool Permute(int[] x,int pos,int[] d,ulong m)
    {
        if(pos==x.Length) return WitnessVerifier.Check(d,m,x,x.Length);
        for(int j=pos;j<x.Length;j++)
        {
            (x[pos],x[j])=(x[j],x[pos]);
            if(Permute(x,pos+1,d,m)) return true;
            (x[pos],x[j])=(x[j],x[pos]);
        }
        return false;
    }
}

