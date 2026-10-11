import SunThreeDeletion.CyclicLarge
import SunThreeDeletion.FiniteBase

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

theorem cyclic_finite_base_zmod (m : ℕ) (hm : 7 ≤ m) (hmax : m ≤ 47) (hodd : Odd m)
    (t : ZMod m) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    HasRainbowCycle ({0,1,t}ᶜ : Set (ZMod m)) := by
  haveI : NeZero m := ⟨by omega⟩
  have ht : 2 ≤ t.val := by
    by_contra h
    have hh : t.val=0 ∨ t.val=1 := by omega
    have hc := ZMod.natCast_zmod_val t
    rcases hh with h | h <;> rw [h] at hc
    · exact ht0 (by simpa using hc.symm)
    · exact ht1 (by simpa using hc.symm)
  simpa only [ZMod.natCast_zmod_val] using cyclic_finite_base m t.val hm hmax hodd ht t.val_lt

theorem cyclic_normalized_units_or_three (m : ℕ) (hodd : Odd m) (hm : 7 ≤ m)
    (t : ZMod m) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hu : IsUnit t ∨ 3*t=0) (hv : IsUnit (t-1) ∨ 3*(t-1)=0) :
    HasRainbowCycle ({0,1,t}ᶜ : Set (ZMod m)) := by
  by_cases hsmall : m ≤ 47
  · exact cyclic_finite_base_zmod m hm hsmall hodd t ht0 ht1
  have hlarge : 49 ≤ m := by obtain ⟨j,hj⟩ := hodd; omega
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact cyclic_large_units m hodd hlarge t ht0 ht1 hu hv
    · have hs0 : (1 : ZMod m)-t ≠ 0 := by simpa [sub_eq_zero] using ht1.symm
      have hs1 : (1 : ZMod m)-t ≠ 1 := by simpa using ht0
      have hs3 : (3 : ZMod m)*(1-t)=0 := by linear_combination -hv
      have h := cyclic_large_order_three m hodd hlarge (1-t) hs0 hs1 hs3
      let neg : ZMod m ≃+ ZMod m := {
        toFun := fun x => -x
        invFun := fun x => -x
        left_inv := neg_neg
        right_inv := neg_neg
        map_add' := neg_add
      }
      have hh := affine_three_cycle neg 1 0 1 (1-t) h
      have heq : ({neg 0+1,neg 1+1,neg (1-t)+1} : Set (ZMod m)) = {0,1,t} := by
        ext x
        simp only [neg, AddEquiv.coe_mk, Equiv.coe_fn_mk, neg_zero, zero_add,
          neg_add_cancel, neg_sub, sub_add_cancel, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [heq] at hh
  · exact cyclic_large_order_three m hodd hlarge t ht0 ht1 hu

end SunThreeDeletion

