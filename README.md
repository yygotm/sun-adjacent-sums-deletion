# Distinct adjacent sums after deleting two, three or four elements of an odd-order abelian group

This repository contains proofs, Lean 4 formalizations and computer checks of three
special cases of a conjecture of Zhi-Wei Sun.

**Conjecture** (Z.-W. Sun, *Some new problems in additive combinatorics*,
arXiv:1309.1679, Conjecture 3.3(i); also Problem 21.130 of the Kourovka Notebook).
Let G be a finite abelian group of odd order and let A be a subset of G with n = |A| > 2.
Then the elements of A can be listed as a_1, ..., a_n so that the n sums

    a_1 + a_2, a_2 + a_3, ..., a_{n-1} + a_n, a_n + a_1

are pairwise distinct.

For A = G and A = G \ {0} (hence A = G \ {a}) this follows from the work of Beals, Gallian,
Headley and Jungreis on harmonious groups (J. Combin. Theory Ser. A 56 (1991) 223-238).

## Results

Let G be a finite abelian group of odd order and D a subset of G with |D| = k.

* **k = 2** (|G| >= 5). For distinct a, b in G, the set G \ {a, b} has such a cyclic
  ordering, and the ordering can be chosen so that its set of adjacent sums is exactly
  G \ {3a - b, 3b - a}.
* **k = 3** (|G| >= 7). For every 3-element D, G \ D has such a cyclic ordering.
* **k = 4** (|G| >= 7). For every 4-element D, G \ D has such a cyclic ordering.

So Sun's conjecture holds whenever |A| >= |G| - 4. There are no exceptional groups in these
ranges (for k = 3, 4 the bound |G| >= 7 is just the condition n > 2). The conjecture for
arbitrary subsets remains open.

| Result | Proof | Lean |
|---|---|---|
| k = 2 | [proofs/two-deletion.md](proofs/two-deletion.md) | `SunTwoDeletion.sun_two_deletion_exact`, `SunTwoDeletion.sun_two_deletion_ordering` |
| k = 3 | [proofs/three-deletion.md](proofs/three-deletion.md) | `SunThreeDeletion.sun_three_deletion` |
| k = 4 | [proofs/four-deletion.md](proofs/four-deletion.md) | `SunFourDeletion.sun_four_deletion` |
| \|A\| = 3, 4, 5; complements of a coset of a subgroup | [proofs/small-sets-and-coset-complements.md](proofs/small-sets-and-coset-complements.md) | not formalized |

The proofs are by induction on |G| through a subgroup H of prime index: the elements of
G \ D are split into cosets of H, a cyclic ordering is built inside each coset (by the
induction hypothesis, by the results for fewer deletions, or, for full cosets, by a
prescribed-edge property of full cyclic orderings that is proved in the documents
themselves), and the pieces are glued along a generator of G/H while keeping track of the
endpoints and of the correction needed when G/H does not split. Cyclic groups and a few
small groups are handled by explicit constructions; the three-element case uses a finite
list of 525 explicit cyclic sequences, which are checked in Lean.

## Contents

```
README.md, LICENSE
proofs/            the four proofs above
lean.md            exact Lean statements, modules, axioms, build instructions
lakefile.toml, lake-manifest.json, lean-toolchain
SunTwoDeletion/, SunThreeDeletion/, SunFourDeletion/, Audit*.lean
                   Lean 4 + Mathlib sources (122 modules)
computation.md     exhaustive searches and checks of the constructions
code/              programs and small result files used in computation.md
FILES.md           inventory of the files
```

## Formal verification

The Lean sources prove the three statements above with no `sorry` and no additional
axioms (`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`).
From the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Details, including the exact statements, are in [lean.md](lean.md).

## Computation

Independently of the proofs, an exhaustive search found such an ordering for every subset
A with |A| >= 3 of every abelian group of odd order at most 35 (21 groups); no
counterexample. Orders up to 31 were also checked by a second, independent implementation
(`code/exhaustive-claude/`). For k = 4, every 4-element deletion was also checked directly
in all 31 abelian groups of odd order 7 to 55. Details are in
[computation.md](computation.md).

## Prior work and novelty

Sun (arXiv:1811.10503, version 6) reports that Yu-Xuan Ji checked the conjecture above
(Conjecture 3.3(i) of arXiv:1309.1679) by computer in 2020 for all abelian groups of odd
order less than 30. The exhaustive search described in the Computation section repeats
this check and extends it to all odd orders at most 35.

We have not found the deletion statements in the literature. We searched the papers citing Sun's
arXiv:1309.1679 and Beals et al. (1991), the papers citing Müyesser and Pokrovskiy,
*A random Hall-Paige conjecture* (Invent. Math. 2025), and the survey of M. A. Ollis,
*Sequenceable groups and related topics* (Electron. J. Combin. Dynamic Survey DS10,
version 3, 2025). For groups that are large compared with k, the k-deletion statement
can also be derived from Theorem 6.9 of Müyesser and Pokrovskiy (no explicit bound on |G|
is given there); the proofs here are elementary and cover all orders. We do not claim
that the results are new.

## How this was made

The proofs, the Lean formalization and the main computations were written by an AI system
(OpenAI GPT, through Codex). The second exhaustive search in `code/exhaustive-claude/` and
the independent reviews of the proofs and of the Lean code were done with another AI
system (Anthropic Claude). The author directed the work and checked the reports but is not
a specialist in this area. Please treat the documents accordingly; the Lean proofs are the
most reliable part.

## Author

Hirotaka Shimizu

## License

MIT (see LICENSE).
