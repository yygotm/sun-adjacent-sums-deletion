import SunTwoDeletion.LiftDeletion
import SunTwoDeletion.Three

set_option autoImplicit false

namespace SunTwoDeletion

universe u

/-- Strengthened induction statement: order three is allowed as a singleton
cycle, so the induction does not exclude a necessary base case. -/
theorem normalized_exact_two_deletion (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0) :
    ∃ c : RainbowCycle ({0, d}ᶜ : Set G),
      c.colors = ({-d, d + d + d}ᶜ : Set G) := by
  suffices h : ∀ n, ∀ (K : Type u) [AddCommGroup K] [Finite K],
      Nat.card K = n → Odd n → ∀ d : K, d ≠ 0 →
      ∃ c : RainbowCycle ({0, d}ᶜ : Set K),
        c.colors = ({-d, d + d + d}ᶜ : Set K) from
    h (Nat.card G) G rfl hodd d hd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard ho d hd
    classical
    have hoddK : Odd (Nat.card K) := hcard.symm ▸ ho
    let L := AddSubgroup.zmultiples d
    by_cases htop : L = ⊤
    · have hgen : ∀ x : K, x ∈ AddSubgroup.zmultiples d := by
        intro x
        change x ∈ L
        rw [htop]
        trivial
      exact normalized_of_generator hoddK d hd hgen
    · letI : Finite (AddSubgroup K) :=
        Finite.of_injective (fun H : AddSubgroup K => (H : Set K)) SetLike.coe_injective
      obtain htop' | ⟨H, hmax, hLH⟩ := eq_top_or_exists_le_coatom L
      · exact (htop htop').elim
      have hdH : d ∈ H := hLH (by exact ⟨1, by simp⟩)
      let dH : H := ⟨d, hdH⟩
      have hdH0 : dH ≠ 0 := fun h => hd (congrArg (fun x : H => (x : K)) h)
      haveI : Nontrivial H := nontrivial_of_ne dH 0 hdH0
      have hH : 3 ≤ Nat.card H := three_le_of_odd_nontrivial H (subgroup_odd hoddK H)
      have hlt : Nat.card H < n := by
        have hh := proper_subgroup_card_lt H hmax.ne_top
        omega
      obtain ⟨cH, hcolorsH⟩ := ih (Nat.card H) hlt H rfl (subgroup_odd hoddK H) dH hdH0
      have hp := maximal_quotient_prime H hmax
      letI : Fact (Nat.card (K ⧸ H)).Prime := ⟨hp⟩
      haveI : IsAddCyclic (K ⧸ H) := isAddCyclic_of_prime_card rfl
      have hq : 3 ≤ Nat.card (K ⧸ H) := by
        have hh := hp.one_lt
        obtain ⟨k, hk⟩ := quotient_odd hoddK H
        omega
      obtain ⟨r, hgen⟩ := quotient_generator_lift H
      exact lift_normalized_deletion hoddK H hH hq r hgen d hd hdH cH hcolorsH

/-- Sun's two-deletion conclusion, including the exact set of adjacent sums. -/
theorem sun_two_deletion_exact (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (_hsize : 2 < Nat.card G - 2)
    (a b : G) (hab : a ≠ b) :
    ∃ c : RainbowCycle ({a, b}ᶜ : Set G),
      c.colors = ({3 • a - b, 3 • b - a}ᶜ : Set G) := by
  obtain ⟨c, hc⟩ := normalized_exact_two_deletion G hodd (b - a) (sub_ne_zero.mpr hab.symm)
  let t := c.translate a
  have hA : (fun x : G => x + a) '' ({0, b - a}ᶜ : Set G) = ({a, b}ᶜ : Set G) := by
    simpa only [zero_add, sub_add_cancel] using translate_compl_pair (0 : G) (b - a) a
  let result : RainbowCycle ({a, b}ᶜ : Set G) :=
    ⟨t.next, (congrArg (fun S : Set G => t.next.IsCycleOn S) hA).mp t.cyclic,
      (congrArg (fun S : Set G => Set.InjOn (fun z => z + t.next z) S) hA).mp t.rainbow⟩
  refine ⟨result, ?_⟩
  have ht : result.colors = t.colors :=
    congrArg (fun S : Set G => (fun x => x + t.next x) '' S) hA.symm
  rw [ht, RainbowCycle.translate_colors, hc, translate_compl_pair]
  have hleft : -(b - a) + (a + a) = 3 • a - b := by abel
  have hright : ((b - a) + (b - a) + (b - a)) + (a + a) = 3 • b - a := by abel
  rw [hleft, hright]

theorem sun_two_deletion (G : Type u) [AddCommGroup G] [Finite G] :
    TwoDeletionStatement G := by
  intro ho hn a b hab
  obtain ⟨c, _⟩ := sun_two_deletion_exact G ho hn a b hab
  exact ⟨c⟩

end SunTwoDeletion
