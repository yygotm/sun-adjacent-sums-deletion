import SunFourDeletion.CosetCoordinates
import SunFourDeletion.FullFiber
import SunFourDeletion.LocalCycles

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem glue_deleted_fibers (hodd : Odd (Nat.card G)) (H : AddSubgroup G) [Fintype H]
    (r : G) (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (hq : 3≤Nat.card (G ⧸ H)) (D : Finset G)
    (hlast : ∀ d∈D, (QuotientAddGroup.mk d : G ⧸ H) ≠
      (Nat.card (G ⧸ H)-1) • QuotientAddGroup.mk r)
    (hsmall : D.card<Nat.card H)
    (hlocal : ∀ i, (productHoles (cosetCoordinates hodd H r hgen) D i).card≤3 ∧
      3≤Nat.card H-(productHoles (cosetCoordinates hodd H r hgen) D i).card) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  classical
  let e := cosetCoordinates hodd H r hgen
  let E := productHoles e D
  have hsum : (∑ i, (E i).card)=D.card := sum_productHoles_card e D
  have hempty : E ⟨Nat.card (G ⧸ H)-1,by omega⟩=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxD := (mem_productHoles e D _ x).mp hx
    apply hlast _ hxD
    exact cosetCoordinates_quotient hodd H r hgen _ x
  have hs : (∑ i : Fin (Nat.card (G ⧸ H)-1),
      (E ⟨i.val,by have := i.isLt; omega⟩).card) < Nat.card H := by
    have hh := sum_fin_prefix_le (Nat.card (G ⧸ H)) (by omega) (fun i => (E i).card)
    omega
  have hc := glue_one_full_fiber hodd H r hgen hq E hempty
    (fun i => small_deletion_cycle (subgroup_odd hodd H) (E i) (hlocal i).1 (hlocal i).2)
    (fun i => by rw [retained_card]; exact (hlocal i).2) hs
  have he := retained_fiber_union e D
  change (⋃ i, (fun x : H => (x : G)+i.val • r) '' ((E i : Set H)ᶜ)) = _ at he
  exact he ▸ hc

end SunFourDeletion
