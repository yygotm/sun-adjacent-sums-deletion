import SunFourDeletion.ProductFibers
import SunThreeDeletion.IndexedEndpoints

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

noncomputable def cosetCoordinates (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r : G) (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r)) :
    (Fin (Nat.card (G ⧸ H)) × H) ≃ G := by
  let e := natOrbit (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen
  apply Equiv.ofBijective (fun p => (p.2 : G)+p.1.val • r)
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hi0 : (QuotientAddGroup.mk' H) (x : G)=0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr x.property
    have hj0 : (QuotientAddGroup.mk' H) (y : G)=0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr y.property
    have hh := congrArg (QuotientAddGroup.mk' H) he
    change (QuotientAddGroup.mk' H) ((x : G)+i.val • r) =
      (QuotientAddGroup.mk' H) ((y : G)+j.val • r) at hh
    rw [map_add,map_add,map_nsmul,map_nsmul,hi0,hj0,zero_add,zero_add] at hh
    have hij : i=j := by
      apply e.injective
      change natOrbit (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen i =
        natOrbit (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen j
      rw [natOrbit_apply,natOrbit_apply]
      exact hh
    subst j
    have hxy : x=y := Subtype.ext (add_right_cancel he)
    subst y
    rfl
  · intro x
    let i := e.symm (QuotientAddGroup.mk x)
    have hi : i.val • (QuotientAddGroup.mk r : G ⧸ H)=QuotientAddGroup.mk x := by
      rw [← natOrbit_apply (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen i]
      exact e.apply_symm_apply _
    have hm : x-i.val • r∈H := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' H) (x-i.val • r)=0
      rw [map_sub,map_nsmul]
      change (QuotientAddGroup.mk x : G ⧸ H)-i.val • QuotientAddGroup.mk r=0
      rw [hi,sub_self]
    exact ⟨(i,⟨x-i.val • r,hm⟩),sub_add_cancel _ _⟩

@[simp] theorem cosetCoordinates_apply (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r : G) (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (i : Fin (Nat.card (G ⧸ H))) (x : H) :
    cosetCoordinates hodd H r hgen (i,x)=(x : G)+i.val • r := rfl

theorem cosetCoordinates_quotient (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r : G) (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (i : Fin (Nat.card (G ⧸ H))) (x : H) :
    (QuotientAddGroup.mk (cosetCoordinates hodd H r hgen (i,x)) : G ⧸ H) =
      i.val • QuotientAddGroup.mk r := by
  change (QuotientAddGroup.mk' H) ((x : G)+i.val • r)=_
  rw [map_add,map_nsmul]
  have hx : (QuotientAddGroup.mk' H) (x : G)=0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr x.property
  rw [hx,zero_add]
  rfl

theorem sum_fin_prefix_le (q : ℕ) (hq : 0<q) (f : Fin q → ℕ) :
    (∑ i : Fin (q-1), f ⟨i.val,by have := i.isLt; omega⟩) ≤ ∑ i : Fin q, f i := by
  cases q with
  | zero => omega
  | succ q =>
    rw [Fin.sum_univ_castSucc]
    exact Nat.le_add_right _ _

end SunFourDeletion
