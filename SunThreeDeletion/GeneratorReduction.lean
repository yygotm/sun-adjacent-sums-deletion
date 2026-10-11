import SunThreeDeletion.CyclicNormalized
import SunThreeDeletion.SeparatedCase
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

def GenOrThree (d : G) : Prop := (∀ x : G, x ∈ AddSubgroup.zmultiples d) ∨ 3 • d=0

theorem small_zmultiples_three (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (hsmall : Nat.card (AddSubgroup.zmultiples d) < 5) : 3 • d=0 := by
  let H := AddSubgroup.zmultiples d
  let dH : H := ⟨d,AddSubgroup.mem_zmultiples d⟩
  have hdH : dH ≠ 0 := fun h => hd (congrArg (fun x : H => (x : G)) h)
  haveI : Nontrivial H := nontrivial_of_ne dH 0 hdH
  have ho := subgroup_odd hodd H
  have hc := three_le_of_odd_nontrivial H ho
  have he : Nat.card H=3 := by obtain ⟨k,hk⟩ := ho; change Nat.card H<5 at hsmall; omega
  have hz : Nat.card H • dH=0 := card_nsmul_eq_zero'
  rw [he] at hz
  exact congrArg (fun x : H => (x : G)) hz

theorem genOrThree_neg (d : G) (hd : GenOrThree d) : GenOrThree (-d) := by
  rcases hd with h | h
  · left
    intro x
    simpa only [AddSubgroup.zmultiples_neg] using h x
  · right
    rw [smul_neg,h,neg_zero]

theorem unit_or_three_of_genOrThree (m : ℕ) (e : ZMod m ≃+ G)
    (d : G) (h : GenOrThree d) :
    IsUnit (e.symm d) ∨ 3*(e.symm d)=0 := by
  rcases h with h | h
  · left
    obtain ⟨k,hk⟩ := h (e 1)
    change k • d = e 1 at hk
    have he := congrArg e.symm hk
    rw [map_zsmul,e.symm_apply_apply] at he
    have hm : (k : ZMod m)*e.symm d=1 := by simpa only [zsmul_eq_mul] using he
    exact ⟨⟨e.symm d,k,by rw [mul_comm]; exact hm,hm⟩,rfl⟩
  · right
    have he := congrArg e.symm h
    simpa only [map_nsmul,map_zero,nsmul_eq_mul,Nat.cast_ofNat] using he

theorem cyclic_from_generator (hodd : Odd (Nat.card G)) (hcard : 7 ≤ Nat.card G)
    (d r : G) (hr0 : r ≠ 0) (hrd : r ≠ d)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d)
    (hr : GenOrThree r) (hrd' : GenOrThree (r-d)) :
    HasRainbowCycle ({0,d,r}ᶜ : Set G) := by
  let e : ZMod (Nat.card G) ≃+ G := zmodAddEquivOfGenerator hgen rfl
  let t := e.symm r
  have he1 : e 1=d := zmodAddEquivOfGenerator_apply_one hgen rfl
  have ht0 : t ≠ 0 := by
    intro h
    apply hr0
    have hh := congrArg e h
    simpa [t] using hh
  have ht1 : t ≠ 1 := by
    intro h
    apply hrd
    have hh := congrArg e h
    simpa only [t,e.apply_symm_apply,he1] using hh
  have hunit := unit_or_three_of_genOrThree (Nat.card G) e r hr
  have hdiff := unit_or_three_of_genOrThree (Nat.card G) e (r-d) hrd'
  have hed : e.symm d=1 := by rw [← he1,e.symm_apply_apply]
  rw [map_sub,hed] at hdiff
  have hc := cyclic_normalized_units_or_three (Nat.card G) hodd hcard t ht0 ht1 hunit hdiff
  have hh := affine_three_cycle e 0 0 1 t hc
  simpa only [map_zero,zero_add,add_zero,he1,t,e.apply_symm_apply] using hh

theorem span_outside (d r : G)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤)
    (hproper : AddSubgroup.zmultiples d ≠ ⊤) : r ∉ AddSubgroup.zmultiples d := by
  intro hr
  apply hproper
  apply top_unique
  rw [← hspan]
  exact sup_le le_rfl (AddSubgroup.zmultiples_le.mpr hr)

theorem shifted_span (d r : G)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤) :
    AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply sup_le
  · apply AddSubgroup.zmultiples_le.mpr
    have hn : -d ∈ AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d) :=
      AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
    simpa only [neg_neg] using (AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d)).neg_mem hn
  · apply AddSubgroup.zmultiples_le.mpr
    have h1 : r-d ∈ AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d) :=
      AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples _)
    have h2 : -d ∈ AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d) :=
      AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
    have h := (AddSubgroup.zmultiples (r-d) ⊔ AddSubgroup.zmultiples (-d)).sub_mem h1 h2
    simpa only [sub_neg_eq_add,sub_add_cancel] using h

end SunThreeDeletion

