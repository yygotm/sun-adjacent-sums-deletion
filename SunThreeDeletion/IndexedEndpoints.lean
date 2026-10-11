import SunTwoDeletion.Orbit
import SunTwoDeletion.QuotientAssembly
import SunTwoDeletion.Displacements
import Mathlib.Tactic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

noncomputable def natOrbit {Q : Type*} [AddCommGroup Q] [Finite Q]
    (hodd : Odd (Nat.card Q)) (r : Q) (hgen : ∀ z : Q, z ∈ AddSubgroup.zmultiples r) :
    Fin (Nat.card Q) ≃ Q := by
  letI := Fintype.ofFinite Q
  exact (finCongr Nat.card_eq_fintype_card).trans (orbitEquiv hodd r hgen)

theorem natOrbit_apply {Q : Type*} [AddCommGroup Q] [Finite Q]
    (hodd : Odd (Nat.card Q)) (r : Q) (hgen : ∀ z : Q, z ∈ AddSubgroup.zmultiples r)
    (i : Fin (Nat.card Q)) :
    natOrbit hodd r hgen i = i.val • r := by
  letI := Fintype.ofFinite Q
  exact orbitEquiv_apply hodd r hgen ((finCongr Nat.card_eq_fintype_card) i)

structure CyclicCosetEndpoints (H : AddSubgroup G) (r : G) where
  x : G ⧸ H → G
  y : G ⧸ H → G
  hx : ∀ i, (QuotientAddGroup.mk (x i) : G ⧸ H) = i
  hy : ∀ i, (QuotientAddGroup.mk (y i) : G ⧸ H) = i
  recurrence : ∀ i, x (i+QuotientAddGroup.mk r) = y i+r

/-- The endpoint construction retains the q*r correction, so it also covers
extensions which are not direct products. -/
theorem endpoints_of_closed_displacements (H : AddSubgroup G)
    (hodd : Odd (Nat.card (G ⧸ H))) (r u : G) (hu : u ∈ H)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (δ : ℕ → G) (hmem : ∀ i, δ i ∈ H)
    (hclose : endpoint u r δ (Nat.card (G ⧸ H)) = u) :
    ∃ E : CyclicCosetEndpoints H r,
      ∀ j : Fin (Nat.card (G ⧸ H)),
        E.x (natOrbit hodd (QuotientAddGroup.mk r) hgen j) = endpoint u r δ j.val ∧
        E.y (natOrbit hodd (QuotientAddGroup.mk r) hgen j) =
          endpoint u r δ j.val + δ j.val := by
  let R : G ⧸ H := QuotientAddGroup.mk r
  let e := natOrbit hodd R hgen
  let x : G ⧸ H → G := fun i => endpoint u r δ (e.symm i).val
  let y : G ⧸ H → G := fun i => x i + δ (e.symm i).val
  have hqpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  have he0 : e ⟨0,hqpos⟩ = 0 := by rw [natOrbit_apply]; simp
  have hx0 : x 0 = u := by
    have hi : e.symm 0 = ⟨0,hqpos⟩ := e.injective (by rw [e.apply_symm_apply, he0])
    simp only [x, hi, endpoint_zero]
  have hx (i) : (QuotientAddGroup.mk (x i) : G ⧸ H) = i := by
    change (QuotientAddGroup.mk (endpoint u r δ (e.symm i).val) : G ⧸ H) = i
    rw [endpoint_quotient H u r hu δ hmem]
    exact (natOrbit_apply hodd R hgen (e.symm i)).symm.trans (e.apply_symm_apply i)
  have hy (i) : (QuotientAddGroup.mk (y i) : G ⧸ H) = i := by
    change (QuotientAddGroup.mk' H) (x i+δ (e.symm i).val) = i
    rw [map_add]
    have hz : (QuotientAddGroup.mk' H) (δ (e.symm i).val) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (hmem _)
    rw [hz, add_zero]
    exact hx i
  have hrec (i) : x (i+R) = y i+r := by
    obtain ⟨j,rfl⟩ := e.surjective i
    by_cases hj : j.val+1 < Nat.card (G ⧸ H)
    · have he : e ⟨j.val+1,hj⟩ = e j+R := by
        rw [natOrbit_apply, natOrbit_apply, succ_nsmul]
      have hi : e.symm (e j+R) = ⟨j.val+1,hj⟩ := by rw [← he, e.symm_apply_apply]
      change endpoint u r δ (e.symm (e j+R)).val =
        (endpoint u r δ (e.symm (e j)).val + δ (e.symm (e j)).val)+r
      rw [hi, e.symm_apply_apply]
      exact endpoint_succ _ _ _ _
    · have hlast : j.val+1 = Nat.card (G ⧸ H) := by have := j.isLt; omega
      have he : e j+R = 0 := by
        rw [natOrbit_apply, ← succ_nsmul, hlast]
        exact card_nsmul_eq_zero'
      rw [he, hx0]
      change u = (endpoint u r δ (e.symm (e j)).val+δ (e.symm (e j)).val)+r
      rw [e.symm_apply_apply, ← endpoint_succ, hlast, hclose]
  refine ⟨⟨x,y,hx,hy,hrec⟩, ?_⟩
  intro j
  simp [x,y,e,R]

end SunThreeDeletion

