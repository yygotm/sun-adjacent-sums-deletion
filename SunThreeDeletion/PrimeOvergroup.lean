import SunThreeDeletion.SeparatedCase
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G] [Finite G]

theorem prime_overgroup (H : AddSubgroup G) (hH : H ≠ ⊤) :
    ∃ (K : AddSubgroup G) (hHK : H ≤ K),
      (Nat.card (K ⧸ H.addSubgroupOf K)).Prime := by
  classical
  have hQ : 1 < Nat.card (G ⧸ H) := by
    have hlt := proper_subgroup_card_lt H hH
    have heq := H.card_eq_card_quotient_mul_card_addSubgroup
    have hp : 0 < Nat.card H := Nat.card_pos
    nlinarith
  let p := (Nat.card (G ⧸ H)).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q,hq⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ H) p (Nat.minFac_dvd _)
  obtain ⟨r,hr⟩ := QuotientAddGroup.mk_surjective q
  let K := H ⊔ AddSubgroup.zmultiples r
  have hHK : H ≤ K := le_sup_left
  let J := H.addSubgroupOf K
  have hmap (x : K) : (QuotientAddGroup.mk x.val : G ⧸ H) ∈ AddSubgroup.zmultiples q := by
    obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp x.property
    obtain ⟨n,hn⟩ := hb
    change n • r=b at hn
    refine ⟨n, ?_⟩
    have hzero : (QuotientAddGroup.mk' H) a=0 := (QuotientAddGroup.eq_zero_iff a).mpr ha
    have hh := congrArg (QuotientAddGroup.mk' H) hab
    rw [map_add,hzero,zero_add,← hn,map_zsmul] at hh
    change n • (QuotientAddGroup.mk r : G ⧸ H) = QuotientAddGroup.mk x.val at hh
    rwa [hr] at hh
  let F : K →+ AddSubgroup.zmultiples q := {
    toFun := fun x => ⟨QuotientAddGroup.mk x.val,hmap x⟩
    map_zero' := Subtype.ext (map_zero (QuotientAddGroup.mk' H))
    map_add' := fun x y => Subtype.ext (map_add (QuotientAddGroup.mk' H) x.val y.val)
  }
  have hFs : Function.Surjective F := by
    rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := hx
    change n • q=x at hn
    refine ⟨⟨n • r, AddSubgroup.mem_sup_right ((AddSubgroup.zmultiples r).zsmul_mem
      (AddSubgroup.mem_zmultiples r) n)⟩, ?_⟩
    apply Subtype.ext
    change (QuotientAddGroup.mk' H) (n • r)=x
    rw [map_zsmul]
    change n • (QuotientAddGroup.mk r : G ⧸ H)=x
    rw [hr,hn]
  have hker : F.ker=J := by
    ext x
    change (⟨QuotientAddGroup.mk x.val,hmap x⟩ : AddSubgroup.zmultiples q)=0 ↔ x.val∈H
    constructor
    · intro h
      exact (QuotientAddGroup.eq_zero_iff x.val).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientAddGroup.eq_zero_iff x.val).mpr h)
  have hc := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective F hFs).toEquiv
  rw [hker,Nat.card_zmultiples,hq] at hc
  exact ⟨K,hHK,hc.symm ▸ hp⟩

end SunThreeDeletion
