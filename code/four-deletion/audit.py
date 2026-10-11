"""Independent witness audit: coordinate tuples, no search code or addition tables."""
import argparse, itertools, json, math, time
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument("witnesses")
p.add_argument("--sample",action="store_true",help="Audit sampled witnesses without claiming exhaustive coverage")
args=p.parse_args()
start=time.monotonic()
groups={}
def decode(x,dims):
    v=[]
    for m in dims: v.append(x%m); x//=m
    assert x==0
    return tuple(v)
def add(a,b,dims): return tuple((x+y)%m for x,y,m in zip(a,b,dims))
def sub(a,b,dims): return tuple((x-y)%m for x,y,m in zip(a,b,dims))
def verify(dims,universe,holes,cycle,expected=None):
    assert len(holes)==4 and len(cycle)==len(universe)-4>2
    assert len(set(cycle))==len(cycle) and set(cycle)==universe-set(holes)
    colors=[add(cycle[i],cycle[(i+1)%len(cycle)],dims) for i in range(len(cycle))]
    assert len(set(colors))==len(colors)
    missing=universe-set(colors)
    if expected is not None: assert missing==set(expected)
    zero=tuple(0 for _ in dims)
    def total(seq):
        s=zero
        for v in seq:s=add(s,v,dims)
        return s
    assert total(missing)==add(total(holes),total(holes),dims)
    return len(colors)
edges=0
with open(args.witnesses,encoding="utf-8-sig") as f:
    for line in f:
        row=json.loads(line);dims=tuple(row["dims"]);n=math.prod(dims)
        if dims not in groups:
            vertices=list(itertools.product(*(range(m) for m in dims)))
            groups[dims]={"universe":set(vertices),"vertices":vertices,"cache":{}}
        g=groups[dims];holes=tuple(decode(x,dims) for x in row["holes"])
        cyc=tuple(decode(x,dims) for x in row["cycle"])
        miss=tuple(decode(x,dims) for x in row["missing"])
        edges+=verify(dims,g["universe"],holes,cyc,miss)
        assert holes[0]==tuple(0 for _ in dims)
        key=frozenset(holes)
        assert key not in g["cache"]
        g["cache"][key]=cyc
if not groups:
    raise SystemExit("no witnesses in input; nothing was audited")
rows=[]
for dims,g in groups.items():
    n=math.prod(dims)
    if args.sample:
        rows.append({"dims":dims,"order":n,"normalized":len(g["cache"]),"sampledWitnesses":len(g["cache"]),"allFourSets":0})
        print(json.dumps(rows[-1]),flush=True)
        continue
    assert len(g["cache"])==math.comb(n-1,3)
    raw=0
    for holes in itertools.combinations(g["vertices"],4):
        anchor=holes[0]
        normalized=frozenset(sub(x,anchor,dims) for x in holes)
        cyc=tuple(add(x,anchor,dims) for x in g["cache"][normalized])
        edges+=verify(dims,g["universe"],holes,cyc)
        raw+=1
    assert raw==math.comb(n,4)
    rows.append({"dims":dims,"order":n,"normalized":len(g["cache"]),"allFourSets":raw})
    print(json.dumps(rows[-1]),flush=True)
result={"pass":True,"complete":True,"input":args.witnesses,"sampleOnly":args.sample,"groups":rows,
        "normalized":sum(x["normalized"] for x in rows),
        "allFourSets":sum(x["allFourSets"] for x in rows),"edges":edges,
        "seconds":time.monotonic()-start}
out=Path("independent-audit-"+Path(args.witnesses).stem+".json")
out.write_text(json.dumps(result,indent=2),encoding="utf-8")
print(json.dumps(result),flush=True)

