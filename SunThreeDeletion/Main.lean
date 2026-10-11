import SunThreeDeletion.LargeSpan
import SunThreeDeletion.SmallSpan
import SunThreeDeletion.Statement

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G] [Finite G]

theorem normalized_three_cycle (hodd : Odd (Nat.card G)) (hcard : 7 ≤ Nat.card G)
    (d r : G) (hd : d≠0) (hr : r≠0) (hdr : d≠r) :
    HasRainbowCycle ({0,d,r}ᶜ : Set G) := by
  let H := AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r
  let dH : H := ⟨d,AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples d)⟩
  let rH : H := ⟨r,AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples r)⟩
  have hdH : dH≠0 := fun h => hd (congrArg (fun x : H => (x:G)) h)
  have hrH : rH≠0 := fun h => hr (congrArg (fun x : H => (x:G)) h)
  have hdrH : dH≠rH := fun h => hdr (congrArg (fun x : H => (x:G)) h)
  by_cases hbig : 7 ≤ Nat.card H
  · have hspan : AddSubgroup.zmultiples dH ⊔ AddSubgroup.zmultiples rH=⊤ := by
      apply top_unique
      intro x _
      obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp x.property
      obtain ⟨i,hi⟩ := ha
      obtain ⟨j,hj⟩ := hb
      have he : i • dH+j • rH=x := by
        apply Subtype.ext
        change i • d+j • r=(x:G)
        change i • d=a at hi
        change j • r=b at hj
        rw [hi,hj,hab]
      rw [← he]
      exact (AddSubgroup.zmultiples dH ⊔ AddSubgroup.zmultiples rH).add_mem
        (AddSubgroup.mem_sup_left ((AddSubgroup.zmultiples dH).zsmul_mem (AddSubgroup.mem_zmultiples dH) i))
        (AddSubgroup.mem_sup_right ((AddSubgroup.zmultiples rH).zsmul_mem (AddSubgroup.mem_zmultiples rH) j))
    have hc := spanning_three_cycle (subgroup_odd hodd H) hbig dH rH hdH hrH hdrH hspan
    have hh := lift_three_cycle hodd H (by omega) 0 dH rH hc
    simpa only [AddSubgroup.coe_zero] using hh
  · haveI : Nontrivial H := nontrivial_of_ne dH 0 hdH
    have h3 := three_le_of_odd_nontrivial H (subgroup_odd hodd H)
    have hs : Nat.card H=3 ∨ Nat.card H=5 := by
      obtain ⟨k,hk⟩ := subgroup_odd hodd H
      omega
    have hh := small_subgroup_three hodd hcard H hs 0 dH rH hdH.symm hrH.symm hdrH
    simpa only [AddSubgroup.coe_zero] using hh

theorem three_deletion_cycle (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G-3)
    (a b c : G) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    HasRainbowCycle ({a,b,c}ᶜ : Set G) := by
  have hc : 7 ≤ Nat.card G := by obtain ⟨k,hk⟩ := hodd; omega
  have hh := normalized_three_cycle hodd hc (b-a) (c-a)
    (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hac.symm)
    (fun h => hbc (sub_left_inj.mp h))
  have hh' := affine_three_cycle (AddEquiv.refl G) a 0 (b-a) (c-a) hh
  simpa only [AddEquiv.refl_apply,zero_add,sub_add_cancel] using hh'

/-- Every three-element deletion in a finite odd-order abelian group admits a
cyclic enumeration with pairwise distinct adjacent sums, including the last-first edge. -/
theorem sun_three_deletion (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G-3)
    (a b c : G) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G-3 ∧ 2 < n ∧
      Set.range v = ({a,b,c}ᶜ : Set G) ∧
      Function.Injective (fun i => v i+v (cyclicSuccessor hn i)) :=
  ordering_of_three_cycle hsize a b c hab hac hbc
    (three_deletion_cycle hodd hsize a b c hab hac hbc)

end SunThreeDeletion
