import SunThreeDeletion.IndexedGlue
import SunThreeDeletion.MappedPaths

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- A sequence of relative endpoints with the full q*r closing correction.
The assembly uses the actual Mathlib quotient, with no splitting hypothesis. -/
theorem glue_relative_cycles (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r : G)
    (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (B : Fin (Nat.card (G ⧸ H)) → Set H)
    (C : ∀ i, RainbowCycle (B i)) (z : ℕ → H)
    (hclose : (z (Nat.card (G ⧸ H)) : G) + Nat.card (G ⧸ H) • r = z 0)
    (hx : ∀ i : Fin (Nat.card (G ⧸ H)), z i.val ∈ B i)
    (hy : ∀ i : Fin (Nat.card (G ⧸ H)), z (i.val+1) ∈ B i)
    (hedge : ∀ i : Fin (Nat.card (G ⧸ H)), (C i).next (z (i.val+1)) = z i.val) :
    HasRainbowCycle (⋃ i : Fin (Nat.card (G ⧸ H)),
      (fun x : H => (x : G)+i.val • r) '' B i) := by
  let δ : ℕ → G := fun i => ((z (i+1)-z i : H) : G)
  have hδ (i) : δ i ∈ H := (z (i+1)-z i).property
  have hep (i : ℕ) : endpoint (z 0 : G) r δ i = (z i : G)+i • r := by
    induction i with
    | zero => simp [endpoint_zero]
    | succ i ih =>
      rw [endpoint_succ,ih,succ_nsmul]
      change (z i : G)+i • r+((z (i+1) : G)-(z i : G))+r = (z (i+1) : G)+(i • r+r)
      abel
  have hc : endpoint (z 0 : G) r δ (Nat.card (G ⧸ H)) = z 0 := by
    rw [hep]
    exact hclose
  apply glue_indexed_paths hodd H r (z 0) (z 0).property hgen δ hδ hc
  · intro i x hx'
    obtain ⟨y,hy',rfl⟩ := hx'
    change (QuotientAddGroup.mk' H) ((y : G)+i.val • r)=_
    rw [map_add,map_nsmul]
    have hz : (QuotientAddGroup.mk' H) (y : G)=0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr y.property
    rw [hz,zero_add]
    rfl
  · intro i
    rw [hep]
    have he : (z i.val : G)+i.val • r+δ i.val = (z (i.val+1) : G)+i.val • r := by
      change (z i.val : G)+i.val • r+((z (i.val+1) : G)-(z i.val : G)) = _
      abel
    rw [he]
    exact path_of_mapped_cycle (C i) H.subtype Subtype.val_injective (i.val • r)
      (z i.val) (z (i.val+1)) (hx i) (hy i) (hedge i)

end SunFourDeletion
