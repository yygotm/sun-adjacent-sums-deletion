# Computational verification

## 1. All subsets through order 35

Write C_n for the cyclic group of order n. Group elements are encoded in mixed radix, with the first cyclic factor as the least significant digit. Counts below are summed across distinct groups.

Every subset of size at least three in every odd-order abelian group of order at most 35 was covered. There are 21 groups: the cyclic groups of odd orders 3 through 35, and C_3^2, C_5^2, C_3 x C_9, and C_3^3. The orders 29, 31, 33, and 35 admit only cyclic abelian groups. There were **zero counterexamples and zero unresolved cases**. For |G| < 30 this repeats a computer check by Yu-Xuan Ji (2020), reported by Z.-W. Sun in arXiv:1811.10503 (version 6).

The search found and independently checked cycles for **1,347,895,475 translation-orbit representatives**. These cover **23,057,487,033 zero-containing subsets** and **46,114,969,695 subsets** without normalization. The range through 29 alone covers 1,017,814,777 subsets using 36,613,853 representatives; orders 31, 33, and 35 contribute 45,097,154,918 subsets using 1,311,281,622 representatives.

| Group | All subsets of size >= 3 | Zero-containing subsets | Orbit representatives | Seconds |
|---|---:|---:|---:|---:|
| C_3 | 1 | 1 | 1 | 0.0557756 |
| C_5 | 16 | 11 | 4 | 0.0007469 |
| C_7 | 99 | 57 | 15 | 0.0005674 |
| C_3 x C_3 | 466 | 247 | 58 | 0.0007892 |
| C_9 | 466 | 247 | 54 | 0.0006188 |
| C_11 | 1,981 | 1,013 | 181 | 0.0009904 |
| C_13 | 8,100 | 4,083 | 624 | 0.0017557 |
| C_15 | 32,647 | 16,369 | 2,183 | 0.0256492 |
| C_17 | 130,918 | 65,519 | 7,702 | 0.0168740 |
| C_19 | 524,097 | 262,125 | 27,585 | 0.0468201 |
| C_21 | 2,096,920 | 1,048,555 | 99,868 | 0.0798854 |
| C_23 | 8,388,331 | 4,194,281 | 364,711 | 0.5438231 |
| C_25 | 33,554,106 | 16,777,191 | 1,342,170 | 0.7174295 |
| C_5 x C_5 | 33,554,106 | 16,777,191 | 1,342,194 | 0.7032928 |
| C_27 | 134,217,349 | 67,108,837 | 4,971,053 | 1.6077039 |
| C_3 x C_3 x C_3 | 134,217,349 | 67,108,837 | 4,971,505 | 1.9071574 |
| C_3 x C_9 | 134,217,349 | 67,108,837 | 4,971,169 | 1.9596228 |
| C_29 | 536,870,476 | 268,435,427 | 18,512,776 | 7.2226789 |
| C_31 | 2,147,483,151 | 1,073,741,793 | 69,273,651 | 29.3289832 |
| C_33 | 8,589,934,030 | 4,294,967,263 | 260,301,158 | 91.7869009 |
| C_35 | 34,359,737,737 | 17,179,869,149 | 981,706,813 | 357.5302695 |

All rows have zero counterexamples and zero unresolved cases. The group times sum to 493.5383347 seconds. Times are elapsed wall-clock times with at most eight workers, including enumeration, normalization, search, witness checking, block output, and final count checks. They exclude compilation, group-table construction, and the separate audit. They are measurements, not runtime guarantees.

## 2. Exhaustiveness and independent checking

The 32-bit program supports odd orders through 31; the 64-bit program supports odd orders through 35. Both use the same search and checking logic.

For a group of order N, the program scans every integer raw in [0,2^(N-1)), forms the subset mask 2*raw+1, and discards sizes one and two. This enumerates exactly the subsets containing zero. Among A-a for a in A, the least bit mask selects a translation-orbit representative. Translating all vertices by t translates all sums by 2t and preserves their distinctness.

For a representative of size s whose translation stabilizer has order h, the orbit contains N/h subsets and s/h subsets containing zero. These weights are added separately at each cardinality and checked against binomial(N,s) and binomial(N-1,s-1). The totals are 2^N-1-N-binomial(N,2) and 2^(N-1)-N.

The search fixes the first vertex at zero, tries the increasing encoding order, and then performs depth-first search, recording unused vertices and used sums in separate masks. The closing sum is tested explicitly. The first budget is 5,000 nodes; retries use four budgets of 20,000 nodes and four of 200,000 nodes. Retry orders are deterministic. Exhausting the budget records an unresolved case, never a counterexample. Every representative was resolved by a valid witness.

`WitnessVerifier.Check` does not use the search addition table, translation routine, or candidate generation. It decodes coordinates again, checks exact vertex coverage without repetitions, and independently computes every cyclic sum, including the closing edge.

The records comprise 44,637 completed blocks. The separate coverage audit checks block identities and contiguous ranges, size counts, empty failure lists, and the Burnside count
```text
number of size-s translation orbits
  = (1/N) * sum over t in G of
      (binomial(N/order(t), s/order(t)) if order(t) divides s, otherwise 0).
```
The included Python `code/audit_all_subsets.py` independently implements these checks. It audits coverage and recorded outcomes, not individual unsaved witnesses.

The all-subset runs do not store every cycle. Each block has a deterministic 64-bit FNV-style digest of representative masks and cycle lists. This is a rerun comparison aid, not a witness certificate or cryptographic proof. Re-running the source regenerates and verifies the cycles. The 32-bit and 64-bit implementations agree on all 5,120 comparison blocks for C_29 and C_3^3, including counts, digests, node counts, and retry counts.

Self-tests compare singleton translations with coordinate arithmetic, verify full-group cycles, and reject invalid length and duplicate vertices. They compare the search with independent permutation enumeration on all 563 zero-containing subsets of size at least three in all five groups of odd order at most nine.

## 3. Four-element deletion through order 55

For all **31 odd-order abelian groups of orders 7 through 55**, every four-element deletion was verified: **2,407,102 four-element sets**, **zero counterexamples**, and **zero unresolved cases**. There are **214,720 saved witnesses** for zero-containing deletion sets. These are all zero-containing four-sets, not one representative per translation orbit.

The range through 35 comprises 19 groups, 35,020 normalized deletion sets, and 250,239 four-element sets. The extension through 55 is exhaustive, not sampled.

| Group | Zero-containing four-sets | All four-sets verified | Seconds |
|---|---:|---:|---:|
| C_7 | 20 | 35 | 0.047467 |
| C_3 x C_3 | 56 | 126 | 0.001532 |
| C_9 | 56 | 126 | 0.001783 |
| C_11 | 120 | 330 | 0.004123 |
| C_13 | 220 | 715 | 0.009833 |
| C_15 | 364 | 1,365 | 0.017659 |
| C_17 | 560 | 2,380 | 0.025112 |
| C_19 | 816 | 3,876 | 0.070787 |
| C_21 | 1,140 | 5,985 | 0.089992 |
| C_23 | 1,540 | 8,855 | 0.215391 |
| C_25 | 2,024 | 12,650 | 0.554742 |
| C_5 x C_5 | 2,024 | 12,650 | 0.910539 |
| C_27 | 2,600 | 17,550 | 0.703772 |
| C_3 x C_3 x C_3 | 2,600 | 17,550 | 0.935297 |
| C_3 x C_9 | 2,600 | 17,550 | 1.096181 |
| C_29 | 3,276 | 23,751 | 1.799638 |
| C_31 | 4,060 | 31,465 | 4.995770 |
| C_33 | 4,960 | 40,920 | 8.497097 |
| C_35 | 5,984 | 52,360 | 12.822558 |
| C_37 | 7,140 | 66,045 | 15.126500 |
| C_39 | 8,436 | 82,251 | 20.676938 |
| C_41 | 9,880 | 101,270 | 26.562677 |
| C_43 | 11,480 | 123,410 | 34.414173 |
| C_3 x C_15 | 13,244 | 148,995 | 79.389871 |
| C_45 | 13,244 | 148,995 | 43.952951 |
| C_47 | 15,180 | 178,365 | 62.982334 |
| C_49 | 17,296 | 211,876 | 80.175674 |
| C_7 x C_7 | 17,296 | 211,876 | 99.823260 |
| C_51 | 19,600 | 249,900 | 102.369930 |
| C_53 | 22,100 | 292,825 | 128.477439 |
| C_55 | 24,804 | 341,055 | 164.047178 |

All rows have zero counterexamples and zero unresolved cases. The recorded total search time of the baseline runs is 891.0138679 seconds; the per-group times in the table sum to 890.80 seconds. The independent Python audits took 244.514 seconds and checked 111,211,048 cyclic edges, counting normalized witnesses and their translated instances.

`Program.cs` enumerates each deletion set {0,d,e,f} with 0<d<e<f, searches its complement with bounded retries, and saves each cycle. A separate coordinate-arithmetic function immediately checks it. The program then enumerates every unordered four-set and checks a translated saved cycle for it.

`audit.py` reads the witnesses without using the search program or its addition tables. It uses coordinate tuples, verifies exact vertex coverage and all cyclic sums, checks the recorded missing-sum set and its sum identity, checks normalized coverage without duplicates, and explicitly checks every unordered four-set by translation. Its `complete` flag refers only to the groups present in its input (and with `--sample`, only to the sampled witnesses); coverage of the full list of groups is checked by `summarize.py`. `summarize.py` independently generates abelian isomorphism types from partitions of prime exponents and checks the group list for omissions and duplicates.

## 4. Checks of the constructive proof

| Check | Cases | Failures |
|---|---:|---:|
| One-full-fiber gluing, eligible normalized inputs and tested quotient representatives, orders <=35 | 1,087,056 | 0 |
| Gluing seams, including wraparound | 4,805,872 | 0 |
| Endpoint orientation repairs exercised | 139,874 | 0 |
| Gluing cases with nonzero q*r | 470,528 | 0 |
| Full four-deletion construction, normalized inputs through 35 | 35,020 | 0 |
| Independent audit of that construction, all four-sets through 35 | 250,239 | 0 |
| Every odd-cardinality subset of every modulus 3 through 21 | 2,096,920 | 0 |
| Cyclic four-deletion construction, normalized inputs, odd orders 23 through 101 | 2,079,200 | 0 |
| Four-image selection, normalized multisets in F_3^2, F_3^3, and F_3^4 | 165 + 3,654 + 91,881 | 0 |
| Direction selection in F_5^2, all four-sets | 12,650 | 0 |
| Affine classification in F_3^2, all four-sets | 126 | 0 |
| Noncyclic construction samples, 18 groups of orders 45 through 243 | 36,000 | 0 |

The last row is a sample, not an exhaustive result through 243. A nonzero q*r does not by itself imply a nonsplit extension. The tests include genuinely nonsplit cases, such as C_27 over its subgroup of order nine.

The gluing tests took 9.4810312 seconds; the construction through 35 took 1.6315146 seconds and its Python audit 16.578 seconds. The larger-group samples took 6.3016678 seconds and their audit 7.25 seconds. The cyclic-subset checks took 5.5005585 seconds.

The three-deletion proof has a finite base of all 525 pairs (n,t) with odd 7<=n<=47 and 2<=t<n. `code/three-deletion/cyclic-finite-certificate.jsonl` is included, not omitted. It gives explicit cycles for C_n minus {0,1,t} with affine template parameters. `verify_certificate.py` checks exact case coverage, vertex coverage, all 15,680 cyclic edges, and the template parameters without searching. The four plane bases and auxiliary one-deletion plane cycle are included as `code/four-deletion/finite-bases.jsonl`. `audit_proof_table.py` verifies the lists printed in `proofs/four-deletion.md` and their affine coverage of all 126 four-sets.

## 5. Source files and reproduction

Requirements: .NET SDK 10.0 or a compatible SDK targeting `net10.0`, and Python 3.9 or later with its standard library. The measurements used .NET SDK 10.0.400 and Microsoft.NETCore.App 10.0.11. No external NuGet package is required.

Included source and project files:

- `code/all-subsets32/Program.cs`
- `code/all-subsets32/SunCheck.csproj`
- `code/all-subsets64/Program.cs`
- `code/all-subsets64/SunCheck.csproj`
- `code/audit_all_subsets.py`
- `code/four-deletion/audit.py`
- `code/four-deletion/audit_proof_table.py`
- `code/four-deletion/Constructor.cs`
- `code/four-deletion/FourConstructor.cs`
- `code/four-deletion/FourDeletion.csproj`
- `code/four-deletion/GeneralGlue.cs`
- `code/four-deletion/ThreeComplete.cs`
- `code/four-deletion/ThreeStructure.cs`
- `code/four-deletion/Program.cs`
- `code/four-deletion/StructuralTests.cs`
- `code/four-deletion/summarize.py`
- `code/three-deletion/verify_certificate.py`

The unsigned reproducibility digest uses unchecked arithmetic. Subset masks are bounded by the supported group order. All output paths are relative. Timings use elapsed wall-clock measurements.

From `code/all-subsets32`:
```sh
dotnet build SunCheck.csproj -c Release
dotnet bin/Release/net10.0/SunCheck.dll --selftest
dotnet bin/Release/net10.0/SunCheck.dll --groups all --threads 8
dotnet bin/Release/net10.0/SunCheck.dll --groups Z29,Z31 --threads 8
python -I ../audit_all_subsets.py runs
```

From `code/all-subsets64`:
```sh
dotnet build SunCheck.csproj -c Release
dotnet bin/Release/net10.0/SunCheck.dll --selftest
dotnet bin/Release/net10.0/SunCheck.dll --groups Z33,Z35 --threads 8
python -I ../audit_all_subsets.py runs
```
The programs resume completed blocks in `runs`. Use a fresh output location for a complete rerun; the 64-bit version accepts `--output-root` and `--chunk-size`. Block widths were 65,536 candidates through order 31 and 1,048,576 for orders 33 and 35. Do not reuse blocks after changing the search algorithm.

From `code/four-deletion`:
```sh
dotnet build FourDeletion.csproj -c Release
dotnet bin/Release/net10.0/FourDeletion.dll baseline 35 7
dotnet bin/Release/net10.0/FourDeletion.dll baseline 45 37
dotnet bin/Release/net10.0/FourDeletion.dll baseline 55 47
dotnet bin/Release/net10.0/FourDeletion.dll glue 35
dotnet bin/Release/net10.0/FourDeletion.dll construct 35
dotnet bin/Release/net10.0/FourDeletion.dll cyclic-test
dotnet bin/Release/net10.0/FourDeletion.dll structure
dotnet bin/Release/net10.0/FourDeletion.dll extra
python -I audit.py witnesses-7-35.jsonl
python -I audit.py witnesses-37-45.jsonl
python -I audit.py witnesses-47-55.jsonl
python -I audit.py construction-witnesses-35.jsonl
python -I audit.py construction-extra-witnesses.jsonl --sample
python -I audit_proof_table.py
python -I summarize.py
```
From the repository root:
```sh
python -I code/three-deletion/verify_certificate.py
```

The JSON summaries in `code/results/` contain the numerical results used in the tables. They are descriptive records; the finite certificate and plane bases contain actual witness lists. Complete enumeration results require regenerating or obtaining the omitted records below.

## 6. Second implementation through order 31

`code/exhaustive-claude/sumcycle.c` is a separate C program, written independently of the programs above and sharing no code with them. For a group given as C_m1 x ... x C_mr it enumerates every subset containing 0 with at least three elements and runs a depth-first search for a cyclic ordering with distinct adjacent sums (the closing sum included). A search that exceeds 2,000,000 nodes is restarted with a random order of the remaining elements, up to 300 times. The environment variables KMIN, KMAX, LIMIT and RESTARTS change the subset sizes and these budgets; `run.sh` clears them so that every run covers all sizes with the default budgets. A subset is counted as `fail` if a complete search finds no ordering, and as `unknown` if the node and restart budget runs out.

It covered all 19 abelian groups of odd order 3 through 31: the cyclic groups of odd orders 3 through 31, and C_3^2, C_5^2, C_3 x C_9, C_3^3. Every group reports `fail=0` and `unknown=0`, and each subset count equals 2^(|G|-1) - |G|, the number of zero-containing subsets with at least three elements. The total is 1,582,650,621 subsets. For orders through 31 these results agree with Section 1.

Limits: the program does not save the orderings it finds and has no separate checker; a found ordering is accepted by the search itself, which tests each new adjacent sum (and the closing sum) against those already used. It is therefore a cross-check of Section 1, not a certificate.

Requirements: Linux, gcc (the program uses `unsigned __int128`) and GNU time. From the repository root:

```sh
bash code/exhaustive-claude/run.sh            # all 19 groups
bash code/exhaustive-claude/run.sh "3" "3 3"  # quick smoke test
```

The program itself exits with status 0 when `fail=0`, even if `unknown>0`. The script therefore checks each summary line, exits with status 1 unless every group reports `fail=0 unknown=0`, and first confirms that a run stopped by the budget (`LIMIT=0`) is rejected. The bundled logs are `out_3-27.log` (orders 3 through 27; for orders 23 through 27 the elapsed time is printed on the line before its group) and `out_29-31.log` (orders 29 and 31, without times). They come from earlier runs of the same source file with simpler scripts that printed the same summary lines, not from `run.sh`, so their layout differs from its output; order 27 took between 77 and 346 seconds per group on the machine used.

## 7. Omitted data files

Large witness files and all-subset block records are not bundled. Dataset names below identify their experiment without a machine-specific location. Byte lengths and SHA-256 values refer to the exact data files. The three-deletion files in this table are supplementary tests; the 525 witnesses required by the finite proof are included separately.

| Dataset | Bytes | SHA-256 |
|---|---:|---|
| `all-subsets/Z11/blocks.jsonl` | 500 | `539b3dd96e7534d848e4946d53671eb437a9197fc3bac5ffc59975f11463a30a` |
| `all-subsets/Z13/blocks.jsonl` | 516 | `5cea16b2e06cb83720cde821d85200dbb362df9ac91f5543cb2453b9761c6f4b` |
| `all-subsets/Z15/blocks.jsonl` | 548 | `b5a76800282d2875684566c6bd7e33293ce289d69bc2cd6dd2f069617297acd6` |
| `all-subsets/Z17/blocks.jsonl` | 582 | `8cf61362ac0637216c49acd6185fae729e9a02829327fe8c632cdb07f95e9bf7` |
| `all-subsets/Z19/blocks.jsonl` | 2,058 | `03ee74496fdbb9850ab0293159c917e95c99ffb5aed104b95e03bfeff5db9698` |
| `all-subsets/Z21/blocks.jsonl` | 8,045 | `417809dd9e83e93e36d5be43823a362e9c84e42006421912f8263ba97228489a` |
| `all-subsets/Z23/blocks.jsonl` | 31,839 | `51320567fc24d9f96870f439e8513891deda5efbe37f4e41566a94998c34688b` |
| `all-subsets/Z25/blocks.jsonl` | 126,781 | `2fb60a8f88e81ab7d760fe539a4bef35dfd328878d2a874b03a61000794d9ddf` |
| `all-subsets/Z27/blocks.jsonl` | 504,977 | `23e9060a05b1ef0febb8428e5a326f62b6b2a87b819d243b27a472008dfec3d6` |
| `all-subsets/Z29/blocks.jsonl` | 2,018,123 | `e525703509c7b31df4da58ac04b81545f240f1484ef080c8aec1bf217df532d8` |
| `all-subsets/Z3/blocks.jsonl` | 450 | `b271d16898791f4a69882832acaa16fcca3910313e3c00ad5afc79f74cc611a1` |
| `all-subsets/Z31/blocks.jsonl` | 8,058,607 | `39d1680125428cd39774bc9206d734c4ca16f13105f7ff27b3660b061887e4e1` |
| `all-subsets/Z33/blocks.jsonl` | 2,865,932 | `bc1dd89a01ce3ce015c777d0f1a9d04b07685b81a08dba1571a905238d1bf0a8` |
| `all-subsets/Z35/blocks.jsonl` | 11,438,369 | `f3e6504edcdcec70be6ce0d702d1007e6ebf4da4d4bfd985e0abe7b6278d0f10` |
| `all-subsets/Z3xZ3/blocks.jsonl` | 477 | `360192524c1f622f5566e4d2a54e128c0f8410adc3d8e2ed976d8fe43460c753` |
| `all-subsets/Z3xZ3xZ3/blocks.jsonl` | 517,942 | `7716dd0b71694e6805074ccb610e822c2442b8b5eaf6d0d27992db7d3c80130c` |
| `all-subsets/Z3xZ9/blocks.jsonl` | 513,288 | `99eb8825bf47aaaa9044a3a957d93c634a7cc381235eff875f0a23494674c327` |
| `all-subsets/Z5/blocks.jsonl` | 455 | `df64d22b19ea964022904343bdd02afd461e6f2aaf7046dc9c28d9f23eca6569` |
| `all-subsets/Z5xZ5/blocks.jsonl` | 130,193 | `6d3c94bdf19fff3341aca3a2ea098ef9043656b27f47864b6d8b10f0c327e6ef` |
| `all-subsets/Z7/blocks.jsonl` | 461 | `feb17d8f75781895bcbf0b04b3bb87a76638fca2293f99b870d06c72609041f6` |
| `all-subsets/Z9/blocks.jsonl` | 476 | `ea91121c343fafb6eea7502eaff6120c33cc7494f9cd17ad83dc38c66172012f` |
| `four-deletion/witnesses-7-35.jsonl` | 5,603,782 | `64f65e13cb6b31b5dbb2a68025f40c04abead1c23f24f5c412bd3f15b2823375` |
| `four-deletion/witnesses-37-45.jsonl` | 12,862,197 | `7a8d9f317fa2c6a1d702eff9c82b68476be6d066b40d961c1acf0f12703df92d` |
| `four-deletion/witnesses-47-55.jsonl` | 26,595,075 | `bd628232bc9743a0d2a59550f8bf1a0ff0a9dde3518d56974f4cfc1c156a70a2` |
| `four-deletion/construction-witnesses-35.jsonl` | 6,046,361 | `97417ba1287e9e8f70a23de3683dc4ff12cc75cba362c73a96e67db89166c421` |
| `four-deletion/construction-extra-witnesses.jsonl` | 18,906,680 | `4fa0a5199d141cc8d299a7b95852cc4c5689f306a382a823e2faeb96cd1945ba` |
| `three-deletion/witnesses.jsonl` | 614,333 | `3631d29fd1412ba2c61b084687b2246dbe9624ea8553f71c430d63d6ee25b7a6` |
| `three-deletion/complete-witnesses.jsonl` | 719,295 | `f5441803fe9aa300ae70c3dac9adeeea1d7292894734ac96b14b209cbc3bd01a` |
| `three-deletion/structural-witnesses.jsonl` | 261,466 | `ce0efce6d8cd3129ca82fc381db829e1d5e822608ab4642297830aec5afe6f1e` |

The same manifest is available as `code/results/omitted-files.json`. No executable, compiled library, build output, or paper PDF is bundled.
