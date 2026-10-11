"""Independent arithmetic audit of the finite lists printed in four-deletion.md."""
import itertools, json, re, time
from pathlib import Path
start=time.monotonic()
def add(a,b):return (a%3+b%3)%3+3*((a//3+b//3)%3)
rows=[]
for line in (Path(__file__).resolve().parents[2]/"proofs"/"four-deletion.md").read_text(encoding="utf-8").splitlines():
    m=re.fullmatch(r"\| ([0-8](?:,[0-8]){3}) \| ([0-8](?:,[0-8]){4}) \| ([0-8](?:,[0-8]){4}) \|",line)
    if m:
        holes,cycle,colors=[list(map(int,s.split(","))) for s in m.groups()]
        assert set(cycle)==set(range(9))-set(holes) and len(set(cycle))==5
        actual=[add(cycle[i],cycle[(i+1)%5]) for i in range(5)]
        assert actual==colors and len(set(colors))==5
        rows.append({"holes":holes,"cycle":cycle,"colors":colors})
assert len(rows)==4
bases={frozenset(x["holes"]):x["cycle"] for x in rows}
coverage={}
for holes in itertools.combinations(range(9),4):
    found=None
    for a,b,c in itertools.permutations(holes,3):
        d=add(b,add(a,a));e=add(c,add(a,a))
        def mul(x,k):
            r=0
            for _ in range(k):r=add(r,x)
            return r
        mapping=[add(a,add(mul(d,i%3),mul(e,i//3))) for i in range(9)]
        if len(set(mapping))!=9:continue
        normalized=frozenset(mapping.index(x) for x in holes)
        if normalized not in bases:continue
        cyc=[mapping[i] for i in bases[normalized]]
        assert set(cyc)==set(range(9))-set(holes)
        assert len({add(cyc[i],cyc[(i+1)%5]) for i in range(5)})==5
        found=",".join(map(str,sorted(normalized)));break
    assert found is not None
    coverage[found]=coverage.get(found,0)+1
one=[1,3,4,7,2,6,8,5]
assert {add(one[i],one[(i+1)%8]) for i in range(8)}==set(range(1,9))
result={"pass":True,"printedBases":rows,"allPlaneFourSets":sum(coverage.values()),
        "coverageByFirstFoundBase":coverage,"oneHolePlane":True,"seconds":time.monotonic()-start}
Path("proof-table-audit.json").write_text(json.dumps(result,indent=2))
print(json.dumps(result))

