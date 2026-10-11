"""Compile result tables and independently check the list of abelian group types."""
import collections,itertools,json,math,time
from pathlib import Path
def read(name):return json.loads(Path(name).read_text(encoding="utf-8-sig"))
def factor(n):
    r={};p=2
    while p*p<=n:
        while n%p==0:r[p]=r.get(p,0)+1;n//=p
        p+=1
    if n>1:r[n]=r.get(n,0)+1
    return r
def parts(n,least=1):
    if n==0:yield ()
    for x in range(least,n+1):
        for rest in parts(n-x,x):yield (x,)+rest
def types(n):
    choices=[[(p,partition) for partition in parts(e)] for p,e in factor(n).items()]
    for choice in itertools.product(*choices):
        yield tuple(sorted((p,exponent) for p,partition in choice for exponent in partition))
def canonical(dims):
    return tuple(sorted((p,e) for n in dims for p,e in factor(n).items()))
ranges=[(7,35),(37,45),(47,55)]
runs=[read(f"baseline-summary-{a}-{b}.json") for a,b in ranges]
assert all(r["completed"] for r in runs)
groups=[g for r in runs for g in r["groups"]]
actual=collections.Counter((g["order"],canonical(g["dims"])) for g in groups)
expected=collections.Counter((n,t) for n in range(7,56,2) for t in types(n))
assert actual==expected and all(v==1 for v in actual.values())
for g in groups:
    n=g["order"]
    assert g["allFourSets"]==g["verified"]==math.comb(n,4)
    assert g["normalized"]==math.comb(n-1,3)
    assert g["normalizedCounterexamples"]==g["normalizedUnknown"]==0
audits=[read(f"independent-audit-witnesses-{a}-{b}.json") for a,b in ranges]
assert all(a["complete"] and a["pass"] for a in audits)
for run,audit in zip(runs,audits):
    assert sum(g["allFourSets"] for g in run["groups"])==audit["allFourSets"]
    assert sum(g["normalized"] for g in run["groups"])==audit["normalized"]
glue=read("general-glue-summary.json")
constructor=read("construction-summary-35.json")
extra=read("construction-extra-summary.json")
structure=read("structural-summary.json")
cyclic=read("cyclic-odd-summary.json")
audit_construction=read("independent-audit-construction-witnesses-35.json")
audit_extra=read("independent-audit-construction-extra-witnesses.json")
tables=read("proof-table-audit.json")
assert all(x.get("completed",x.get("complete",False)) for x in [glue,constructor,extra,structure,cyclic,audit_construction,audit_extra])
assert tables["pass"] and audit_construction["pass"] and audit_extra["pass"]
result={"complete":True,"isomorphismTypes":len(groups),
        "allFourSets":sum(g["allFourSets"] for g in groups),
        "normalized":sum(g["normalized"] for g in groups),
        "counterexamples":0,"unknown":0,"searchSeconds":sum(r["seconds"] for r in runs),
        "independentAuditSeconds":sum(a["seconds"] for a in audits),
        "independentEdges":sum(a["edges"] for a in audits),
        "gluingCases":sum(g["Trials"] for g in glue["groups"]),
        "gluingSeams":sum(g["Seams"] for g in glue["groups"]),
        "gluingOrientationRepairs":sum(g["Repairs"] for g in glue["groups"]),
        "gluingNonzeroQrCases":sum(g["NonzeroQr"] for g in glue["groups"]),
        "constructionNormalizedThrough35":sum(g["count"] for g in constructor["groups"]),
        "extraSamples":sum(g["sampledNormalizedFourSets"] for g in extra["groups"]),
        "maxExtraOrder":max(g["order"] for g in extra["groups"])}
Path("verification-summary.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
table=["| Group | Normalized four-sets | All four-sets verified | Counterexamples | Unknown | Seconds |",
       "|---|---:|---:|---:|---:|---:|"]
for g in groups:
    table.append(f'| {g["group"]} | {g["normalized"]:,} | {g["allFourSets"]:,} | 0 | 0 | {g["seconds"]:.6f} |')
Path("per-group-results.md").write_text("\n".join(table)+"\n",encoding="utf-8")
print(json.dumps(result))

