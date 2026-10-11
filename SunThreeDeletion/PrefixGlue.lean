import SunThreeDeletion.PrefixDisplacements
import SunThreeDeletion.IndexedGlue
import SunTwoDeletion.EdgeProperty

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- A finite prescribed sequence of punctured paths can be followed by full coset
paths. If only one full coset remains, the nonzero residual is stated explicitly. -/
theorem glue_prefix_paths (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (r u : G) (hu : u ∈ H)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (pre : List H) (hq : pre.length+1 ≤ Nat.card (G ⧸ H))
    (hres : pre.length+1 = Nat.card (G ⧸ H) →
      -(Nat.card (G ⧸ H) • r) ≠ (pre.sum : G))
    (A : Fin (Nat.card (G ⧸ H)) → Set G)
    (hA : ∀ j z, z ∈ A j →
      (QuotientAddGroup.mk z : G ⧸ H) = j.val • (QuotientAddGroup.mk r : G ⧸ H))
    (paths : ∀ j, j.val < pre.length →
      RainbowPath (A j) (endpoint u r (fun i => (pre.getD i 0 : G)) j.val)
        (endpoint u r (fun i => (pre.getD i 0 : G)) j.val + (pre.getD j.val 0 : G)))
    (full : ∀ j, pre.length ≤ j.val →
      A j = {z | (QuotientAddGroup.mk z : G ⧸ H) =
        j.val • (QuotientAddGroup.mk r : G ⧸ H)}) :
    HasRainbowCycle (⋃ j, A j) := by
  classical
  letI := Fintype.ofFinite H
  let q := Nat.card (G ⧸ H)
  let target : H := ⟨-(q • r), H.neg_mem (quotient_card_nsmul_mem H r)⟩
  have hres' (heq : pre.length+1=q) : target-pre.sum ≠ 0 := by
    intro h
    apply hres heq
    exact congrArg (fun x : H => (x : G)) (sub_eq_zero.mp h)
  obtain ⟨δ,hpre,hsum,hne⟩ := displacements_with_prefix_one_or_more
    (by simpa only [Nat.card_eq_fintype_card] using hH) pre q hq target hres'
  let ε : ℕ → G := fun i => (pre.getD i 0 : G)
  let D : ℕ → G := fun i => (δ i : G)
  have hD (i : ℕ) (hi : i < pre.length) : D i = ε i :=
    congrArg (fun x : H => (x : G)) (hpre i hi)
  have hep (i : ℕ) (hi : i ≤ pre.length) :
      endpoint u r D i = endpoint u r ε i :=
    endpoint_congr_prefix u r D ε i (fun j hj => hD j (by omega))
  have hclose : endpoint u r D q = u := by
    apply endpoint_closes
    have h := congrArg (fun x : H => (x : G)) hsum
    simpa [D, target] using h
  apply glue_indexed_paths hodd H r u hu hgen D (fun i => (δ i).property) hclose A hA
  intro j
  by_cases hj : j.val < pre.length
  · rw [hep j.val (by omega), hD j.val hj]
    exact paths j hj
  · rw [full j (by omega)]
    have hx := endpoint_quotient H u r hu D (fun i => (δ i).property) j.val
    have hy : (QuotientAddGroup.mk (endpoint u r D j.val+D j.val) : G ⧸ H) =
        (QuotientAddGroup.mk (endpoint u r D j.val) : G ⧸ H) := by
      change (QuotientAddGroup.mk' H) (_+_) = _
      rw [map_add]
      have hz : (QuotientAddGroup.mk' H) (D j.val) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr (δ j.val).property
      rw [hz, add_zero]
      rfl
    have hxy : endpoint u r D j.val ≠ endpoint u r D j.val+D j.val := by
      intro heq
      apply hne j.val (by omega) j.isLt
      apply Subtype.ext
      change (δ j.val : G) = (0 : G)
      have hh : D j.val = 0 := (add_eq_left.mp heq.symm)
      exact hh
    let P := Classical.choice (coset_path_exists H (edge_property_odd H (subgroup_odd hodd H))
      (endpoint u r D j.val) (endpoint u r D j.val+D j.val) hxy hy.symm)
    rw [hx] at P
    exact P

end SunThreeDeletion

