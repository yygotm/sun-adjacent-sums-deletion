import SunThreeDeletion.GeneratorReduction
import SunThreeDeletion.ElementaryThree

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem genOrThree_of_failure (hodd : Odd (Nat.card G))
    (d r : G) (hd : d ≠ 0)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤)
    (hfail : ¬ HasRainbowCycle ({0,d,r}ᶜ : Set G)) : GenOrThree d := by
  by_cases htop : AddSubgroup.zmultiples d = ⊤
  · left
    intro x
    rw [htop]
    trivial
  by_cases hbig : 5 ≤ Nat.card (AddSubgroup.zmultiples d)
  · exfalso
    apply hfail
    let dH : AddSubgroup.zmultiples d := ⟨d,AddSubgroup.mem_zmultiples d⟩
    have hdH : dH ≠ 0 := fun h => hd (congrArg (fun x : AddSubgroup.zmultiples d => (x : G)) h)
    exact separated_from_cyclic_subgroup hodd (AddSubgroup.zmultiples d) hbig dH hdH r
      (span_outside d r hspan htop)
  · exact Or.inr (small_zmultiples_three hodd d hd (by omega))

theorem spanning_three_cycle (hodd : Odd (Nat.card G)) (hcard : 7 ≤ Nat.card G)
    (d r : G) (hd : d ≠ 0) (hr : r ≠ 0) (hdr : d ≠ r)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤) :
    HasRainbowCycle ({0,d,r}ᶜ : Set G) := by
  by_contra hfail
  have hswap : ¬ HasRainbowCycle ({0,r,d}ᶜ : Set G) := by
    have hs : ({0,r,d} : Set G) = {0,d,r} := by ext x; simp [or_comm,or_left_comm]
    rwa [hs]
  have hshift : ¬ HasRainbowCycle ({0,r-d,-d}ᶜ : Set G) := by
    intro hc
    have hh := affine_three_cycle (AddEquiv.refl G) d 0 (r-d) (-d) hc
    have hs : ({0+d,(r-d)+d,-d+d} : Set G) = {0,d,r} := by
      ext x
      simp only [zero_add,sub_add_cancel,neg_add_cancel,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    apply hfail
    simpa only [AddEquiv.refl_apply,hs] using hh
  have hdC := genOrThree_of_failure hodd d r hd hspan hfail
  have hrC := genOrThree_of_failure hodd r d hr (by simpa only [sup_comm] using hspan) hswap
  have hrd : r-d ≠ 0 := sub_ne_zero.mpr hdr.symm
  have hrdC := genOrThree_of_failure hodd (r-d) (-d) hrd (shifted_span d r hspan) hshift
  rcases hdC with hgen | hd3
  · exact hfail (cyclic_from_generator hodd hcard d r hr hdr.symm hgen hrC hrdC)
  rcases hrC with hgen | hr3
  · have hneg : GenOrThree (d-r) := by
      have hn := genOrThree_neg (r-d) hrdC
      simpa only [neg_sub] using hn
    exact hswap (cyclic_from_generator hodd hcard r d hd hdr hgen (Or.inr hd3) hneg)
  rcases hrdC with hgen | hrd3
  · have hne : -d ≠ r-d := by
      intro h
      apply hr
      calc
        r = (r-d)+d := by abel
        _ = 0 := by rw [← h]; abel
    have hc1 := genOrThree_neg d (Or.inr hd3)
    have hc2 : GenOrThree (-d-(r-d)) := by
      have heq : -d-(r-d) = -r := by abel
      rw [heq]
      exact genOrThree_neg r (Or.inr hr3)
    exact hshift (cyclic_from_generator hodd hcard (r-d) (-d) (neg_ne_zero.mpr hd) hne hgen hc1 hc2)
  by_cases htop : AddSubgroup.zmultiples d = ⊤
  · have hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d := by intro x; rw [htop]; trivial
    exact hfail (cyclic_from_generator hodd hcard d r hr hdr.symm hgen (Or.inr hr3) (Or.inr hrd3))
  · exact hfail (independent_three_cycle hodd d r hd hd3 hr3 (span_outside d r hspan htop) hspan)

end SunThreeDeletion

