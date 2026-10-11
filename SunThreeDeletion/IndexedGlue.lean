import SunThreeDeletion.IndexedEndpoints

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Glue any collection of (possibly punctured) coset paths whose endpoints close.
All quotient indexing uses Mathlib's actual quotient group. -/
theorem glue_indexed_paths (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r u : G) (hu : u ∈ H)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (δ : ℕ → G) (hmem : ∀ i, δ i ∈ H)
    (hclose : endpoint u r δ (Nat.card (G ⧸ H)) = u)
    (A : Fin (Nat.card (G ⧸ H)) → Set G)
    (hA : ∀ j z, z ∈ A j →
      (QuotientAddGroup.mk z : G ⧸ H) = j.val • (QuotientAddGroup.mk r : G ⧸ H))
    (paths : ∀ j, RainbowPath (A j) (endpoint u r δ j.val)
      (endpoint u r δ j.val+δ j.val)) :
    HasRainbowCycle (⋃ j, A j) := by
  let e := natOrbit (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen
  obtain ⟨E,hE⟩ := endpoints_of_closed_displacements H (quotient_odd hodd H) r u hu hgen δ hmem hclose
  have hex (i : G ⧸ H) : E.x i = endpoint u r δ (e.symm i).val := by
    have hh := (hE (e.symm i)).1
    change E.x (e (e.symm i)) = _ at hh
    simpa only [e.apply_symm_apply] using hh
  have hey (i : G ⧸ H) : E.y i = endpoint u r δ (e.symm i).val+δ (e.symm i).val := by
    have hh := (hE (e.symm i)).2
    change E.y (e (e.symm i)) = _ at hh
    simpa only [e.apply_symm_apply] using hh
  let P : CosetPaths H r := {
    A := fun i => A (e.symm i)
    x := E.x
    y := E.y
    hx := E.hx
    hy := E.hy
    recurrence := E.recurrence
    path := fun i => by
      rw [hex i, hey i]
      exact paths (e.symm i)
    coset := fun i z hz => by
      rw [hA (e.symm i) z hz]
      exact (natOrbit_apply (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen
        (e.symm i)).symm.trans (e.apply_symm_apply i)
  }
  have heq : (⋃ i, P.A i) = ⋃ j, A j := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e.symm i,hi⟩
    · rintro ⟨j,hj⟩
      exact ⟨e j, by simpa only [P, e.symm_apply_apply] using hj⟩
  exact ⟨heq ▸ P.assemble hodd hgen⟩

end SunThreeDeletion

