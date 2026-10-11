import SunTwoDeletion.Displacements
import SunTwoDeletion.Orbit

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

structure ClosedCosetEndpoints (H : AddSubgroup G) (r u v : G) where
  x : G ⧸ H → G
  y : G ⧸ H → G
  hx : ∀ i, (QuotientAddGroup.mk (x i) : G ⧸ H) = i
  hy : ∀ i, (QuotientAddGroup.mk (y i) : G ⧸ H) = i
  recurrence : ∀ i, x (i + QuotientAddGroup.mk r) = y i + r
  x_zero : x 0 = u
  y_zero : y 0 = v
  distinct : ∀ i, i ≠ 0 → x i ≠ y i

theorem closed_endpoints_exist (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (hq : 3 ≤ Nat.card (G ⧸ H)) (r u v : G)
    (hu : u ∈ H) (hv : v ∈ H)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r)) :
    Nonempty (ClosedCosetEndpoints H r u v) := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  let R : G ⧸ H := QuotientAddGroup.mk r
  let e := orbitEquiv (quotient_odd hodd H) R hgen
  have hqpos : 0 < Fintype.card (G ⧸ H) := Fintype.card_pos
  let zeroIndex : Fin (Fintype.card (G ⧸ H)) := ⟨0, hqpos⟩
  have he0 : e zeroIndex = 0 := orbitEquiv_zero _ _ _ _
  have he0' : e.symm 0 = zeroIndex := by
    apply e.injective
    rw [e.apply_symm_apply, he0]
  obtain ⟨δ, hfirst, hmem, hnonzero, hclose⟩ :=
    exists_closed_displacements H hH r u v hu hv (quotient_odd hodd H) hq
  let x : G ⧸ H → G := fun i => endpoint u r δ (e.symm i).val
  let y : G ⧸ H → G := fun i => x i + δ (e.symm i).val
  have hx0 : x 0 = u := by
    dsimp [x]
    rw [he0']
    exact endpoint_zero _ _ _
  have hy0 : y 0 = v := by
    change x 0 + δ (e.symm 0).val = v
    rw [hx0, he0']
    change u + δ 0 = v
    rw [hfirst]
    abel
  have hx : ∀ i, (QuotientAddGroup.mk (x i) : G ⧸ H) = i := by
    intro i
    change (QuotientAddGroup.mk (endpoint u r δ (e.symm i).val) : G ⧸ H) = i
    rw [endpoint_quotient H u r hu δ hmem]
    exact (orbitEquiv_apply _ _ _ (e.symm i)).symm.trans (e.apply_symm_apply i)
  have hy : ∀ i, (QuotientAddGroup.mk (y i) : G ⧸ H) = i := by
    intro i
    change (QuotientAddGroup.mk' H) (x i + δ (e.symm i).val) = i
    rw [map_add]
    have hz : (QuotientAddGroup.mk' H) (δ (e.symm i).val) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (hmem _)
    rw [hz, add_zero]
    exact hx i
  have hrec : ∀ i, x (i + R) = y i + r := by
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    by_cases hj : j.val + 1 < Fintype.card (G ⧸ H)
    · have hnext : e ⟨j.val + 1, hj⟩ = e j + R := orbitEquiv_succ _ _ _ j hj
      have hindex : e.symm (e j + R) = ⟨j.val + 1, hj⟩ := by
        rw [← hnext, e.symm_apply_apply]
      change endpoint u r δ (e.symm (e j + R)).val =
        (endpoint u r δ (e.symm (e j)).val + δ (e.symm (e j)).val) + r
      rw [hindex, e.symm_apply_apply]
      exact endpoint_succ _ _ _ _
    · have hlast : e j + R = 0 := orbitEquiv_last _ _ _ j hj
      rw [hlast, hx0]
      change u = (endpoint u r δ (e.symm (e j)).val + δ (e.symm (e j)).val) + r
      rw [e.symm_apply_apply]
      have hcard : j.val + 1 = Nat.card (G ⧸ H) := by
        rw [Nat.card_eq_fintype_card]
        have := j.isLt
        omega
      calc
        u = endpoint u r δ (Nat.card (G ⧸ H)) := hclose.symm
        _ = endpoint u r δ j.val + δ j.val + r := by rw [← hcard, endpoint_succ]
  have hdistinct : ∀ i, i ≠ 0 → x i ≠ y i := by
    intro i hi hxy
    have hn : 0 < (e.symm i).val := by
      by_contra h
      have heq : e.symm i = zeroIndex := Fin.ext (by dsimp [zeroIndex]; omega)
      apply hi
      calc
        i = e (e.symm i) := (e.apply_symm_apply i).symm
        _ = e zeroIndex := congrArg e heq
        _ = 0 := he0
    have hlt : (e.symm i).val < Nat.card (G ⧸ H) := by
      simpa only [Nat.card_eq_fintype_card] using (e.symm i).isLt
    apply hnonzero _ hn hlt
    change x i = x i + δ (e.symm i).val at hxy
    exact (add_left_cancel (show x i + 0 = x i + δ (e.symm i).val by simpa using hxy)).symm
  exact ⟨⟨x, y, hx, hy, hrec, hx0, hy0, hdistinct⟩⟩

end SunTwoDeletion
