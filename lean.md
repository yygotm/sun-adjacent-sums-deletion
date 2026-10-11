# Lean formalization

## 1. Scope and build

The three libraries prove two-, three-, and four-element deletion for finite
abelian groups of odd order. They include all group orders for which the
remaining set has more than two elements. The two-deletion theorem also
specifies the exact set of adjacent sums. The three- and four-deletion theorems
assert existence without prescribing the missing sums.

The repository is a single Lake project. Install Lean through Elan, then run
these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The first command obtains the Mathlib cache; the second builds all four
declared libraries, including the audit modules. The third displays the
theorem checks and axiom reports even when the build is already up to date.
The first run needs network access for dependencies and their cache.

`lean-toolchain` selects `leanprover/lean4:v4.34.1`. The Mathlib dependency in
`lakefile.toml` is pinned as follows:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.34.1"
```

The corresponding Mathlib commit is
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The package contains source files only; dependency caches and compiler outputs
are created by the build, rather than distributed with it.

## 2. Meaning of the cyclic-ordering contract

Write `N = Nat.card G`. For deletion of `k` elements, the conclusion produces
`n = N - k`, a proof `hn : 0 < n`, and an embedding `v : Fin n ↪ G`.
The embedding is injective, and its range is exactly the required complement.
The conclusion explicitly includes `2 < n`.

The successor is defined in `SunTwoDeletion/Ordering.lean`:

```lean
def cyclicSuccessor {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, hn⟩
```

The theorem `cyclicSuccessor_val` proves that its value is
`(i.val + 1) % n`. Thus injectivity of
`fun i => v i + v (cyclicSuccessor hn i)` checks all `n` cyclic edges,
including the edge from the last vertex back to the first.

Internally, `SunTwoDeletion.RainbowCycle A` consists of a permutation of `G`
whose restriction is a single cycle on `A`, together with injectivity on `A`
of `x ↦ x + next x`. Its `colors` field notation denotes the image of this
sum map. The indexing theorem converts that permutation into the explicit
`Fin n` enumeration; no enumeration assumption is supplied by the caller.

## 3. Two-element deletion

Public import: `SunTwoDeletion`.
The exact theorem is in `SunTwoDeletion/Main.lean`:

```lean
theorem SunTwoDeletion.sun_two_deletion_exact
    (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (_hsize : 2 < Nat.card G - 2)
    (a b : G) (hab : a ≠ b) :
    ∃ c : SunTwoDeletion.RainbowCycle ({a, b}ᶜ : Set G),
      c.colors = ({3 • a - b, 3 • b - a}ᶜ : Set G)
```

The indexed theorem is in `SunTwoDeletion/Ordering.lean`:

```lean
theorem SunTwoDeletion.sun_two_deletion_ordering
    (G : Type*) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G - 2)
    (a b : G) (hab : a ≠ b) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G - 2 ∧ 2 < n ∧
      Set.range v = ({a, b}ᶜ : Set G) ∧
      Function.Injective
        (fun i => v i + v (SunTwoDeletion.cyclicSuccessor hn i)) ∧
      Set.range
        (fun i => v i + v (SunTwoDeletion.cyclicSuccessor hn i)) =
        ({3 • a - b, 3 • b - a}ᶜ : Set G)
```

These hypotheses cover every odd `N ≥ 5`.
The stronger internal induction includes an order-three singleton cycle;
this auxiliary case is used in lifting, while the public ordering has
strictly more than two vertices.

## 4. Three-element deletion

Public import: `SunThreeDeletion`.
The theorem is in `SunThreeDeletion/Main.lean`:

```lean
theorem SunThreeDeletion.sun_three_deletion
    {G : Type*} [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G - 3)
    (a b c : G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G - 3 ∧ 2 < n ∧
      Set.range v = ({a, b, c}ᶜ : Set G) ∧
      Function.Injective
        (fun i => v i + v (SunTwoDeletion.cyclicSuccessor hn i))
```

These hypotheses cover every odd `N ≥ 7`.
The cyclic constructions `Q_(4k+1)` and `Q_(4k+3)` are verified directly:
the four runs, their boundary edges, and the coverage of nonzero colors are
proved in Lean. The exceptional boundary lists are derived from endpoint
inequalities. All 525 finite cyclic certificates, for odd moduli from 7
through 47, are checked with ordinary `decide`, as are six further
small-group certificates. No theorem from the literature or external search
output is assumed as an axiom.

The formalized scope is the existence and ordering conclusion above.
It does not include every additional exact-color formula or obstruction
discussed in the prose proof.

## 5. Four-element deletion

Public import: `SunFourDeletion`.
The theorem is in `SunFourDeletion/Main.lean`:

```lean
theorem SunFourDeletion.sun_four_deletion
    {G : Type u} [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 7 ≤ Nat.card G)
    (a b c d : G)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G - 4 ∧ 2 < n ∧
      Set.range v = ({a, b, c, d}ᶜ : Set G) ∧
      Function.Injective
        (fun i => v i + v (SunTwoDeletion.cyclicSuccessor hn i))
```

The boundary `N = 7` is included. There are no exceptional groups.
`SunFourDeletion.sun_four_deletion_finset` provides the equivalent interface
with `D : Finset G` and `D.card = 4`.

The proof uses an explicit construction for odd-sized subsets of cyclic
groups and a gluing lemma with one full fiber. Its endpoint argument applies
to any number of holes smaller than the subgroup order, provided that the
required local cycles exist. The closing equation contains `q • r`;
no direct-product decomposition is assumed.

The small plane of order 9 is covered by 56 explicit certificates for deletion
sets containing zero. The directional assertions in the planes of orders 9
and 25 are checked by kernel reduction over finite coordinate types. These
checks prove the finite facts inside Lean; their correctness does not depend
on running a separate search program.

## 6. Modules and induction

There are **122 Lean source modules**:

| Module family | Number | Contents |
|---|---:|---|
| `SunTwoDeletion/` | 25 | Rainbow cycles, prescribed edges, endpoint closure, cyclic quotient gluing, exact deletion, conversion to an indexed ordering |
| `SunThreeDeletion/` | 62 | Direct nonzero cyclic constructions, run boundaries, punctured fibers, subgroup lifting, finite certificates, cyclic and affine-span cases, main theorem |
| `SunFourDeletion/` | 28 | Odd cyclic subsets, endpoint avoidance, one-full-fiber gluing, quotient selection, small planes, strict induction, main theorem |
| Public imports | 3 | `SunTwoDeletion.lean`, `SunThreeDeletion.lean`, `SunFourDeletion.lean` |
| Audit modules | 4 | `Audit.lean`, `AuditTwo.lean`, `AuditThree.lean`, `AuditExamples.lean` |

The 62 three-deletion modules include the 21 files
`SunThreeDeletion/FiniteBase/N7.lean` through `N47.lean`, one for each odd modulus.

All subgroup and quotient arguments use Mathlib's `AddSubgroup` and actual
quotient groups. Prescribed-edge existence is proved independently before
the two-deletion induction uses it. In four-deletion induction, four holes
in a single fiber invoke the theorem only in a proper subgroup of strictly
smaller cardinality. Otherwise each local problem has at most three holes,
so it uses an already established theorem. The one-hole input has a separate
induction. No circular induction hypothesis or unproved classification is
an argument of any public theorem.

## 7. Axiom reports and audit examples

The main theorem reports are:

```text
'SunTwoDeletion.sun_two_deletion_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunTwoDeletion.sun_two_deletion_ordering' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunThreeDeletion.sun_three_deletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunFourDeletion.sun_four_deletion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical dependencies. The source uses no `sorry`,
`admit`, new `axiom`, `native_decide`, `Lean.ofReduceBool`, or `unsafe`.
The finite proofs use kernel-checked reduction rather than a trusted native
computation primitive.

`AuditThree.lean` and `Audit.lean` independently spell the output contract
using the fixed length `Nat.card G - k` and the literal modulo successor.
This checks the meaning of the public statement as well as its derivation.
`Audit.lean` also instantiates four-deletion in `ZMod 9` and at the boundary
`ZMod 7`.

The explicit positive example in `AuditExamples.lean` is the ordering
`[4,5,6,7,8]` of `ZMod 9` after deleting `{0,1,2,3}`. Its cyclic sums are
`[0,2,4,6,3]`, which are all distinct.

The negative control is `[4,5,6,8,7]`. It has exactly the same distinct
vertices and pairwise distinct internal sums `[0,2,5,6]`. Its closing sum
is `7 + 4 = 2`, repeating the internal sum `5 + 6 = 2` modulo 9.
Lean proves both the internal-sum assertion and rejection by the same
`RainbowEnumeration` predicate used to specify a valid enumeration.
`SunFourDeletion.badNine_rejected` depends only on `[propext, Quot.sound]`.

The formal existence theorems do not assert the full arbitrary-subset
conjecture, a prescribed missing-sum set for three or four deletions, or an
arbitrary-number-of-deletions theorem.
