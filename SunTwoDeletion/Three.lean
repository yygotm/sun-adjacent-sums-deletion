import SunTwoDeletion.Deletion

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem generator_three_card (d : G) (hd : d ≠ 0)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d)
    (h3 : d + d + d = 0) : Nat.card G = 3 := by
  have hs : (3 : ℕ) • d = 0 := by simpa only [succ_nsmul, zero_nsmul, zero_add] using h3
  have hv := addOrderOf_dvd_of_nsmul_eq_zero hs
  rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen] at hv
  haveI : Nontrivial G := nontrivial_of_ne d 0 hd
  have hgt := Finite.one_lt_card (α := G)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hv with h | h
  · omega
  · exact h

theorem three_elements (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (hcard : Nat.card G = 3) : ∀ x : G, x = 0 ∨ x = d ∨ x = d + d := by
  classical
  letI := Fintype.ofFinite G
  have h20 : d + d ≠ 0 := fun h => hd (double_injective hodd (by simpa using h))
  have h21 : d + d ≠ d := by simpa using hd
  have htriple : ({0, d, d + d} : Finset G).card = 3 := by
    simp [hd, h20, h21, hd.symm, h20.symm, h21.symm]
  have hall : ({0, d, d + d} : Finset G) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, htriple, ← Nat.card_eq_fintype_card, hcard]
  intro x
  have hx : x ∈ ({0, d, d + d} : Finset G) := hall.symm ▸ Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

/-- The order-three base is deliberately a singleton with its doubled color. -/
theorem normalized_three (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) (h3 : d + d + d = 0) :
    ∃ c : RainbowCycle ({0, d}ᶜ : Set G),
      c.colors = ({-d, d + d + d}ᶜ : Set G) := by
  have hcard := generator_three_card d hd hgen h3
  have hall := three_elements hodd d hd hcard
  have h20 : d + d ≠ 0 := fun h => hd (double_injective hodd (by simpa using h))
  have h21 : d + d ≠ d := by simpa using hd
  have hneg : -d = d + d := (eq_neg_of_add_eq_zero_left h3).symm
  have hA : ({0, d}ᶜ : Set G) = {d + d} := by
    ext x
    rcases hall x with rfl | rfl | rfl <;> simp [hd, h20, h21, h20.symm]
  have hC : ({-d, d + d + d}ᶜ : Set G) = {d} := by
    rw [hneg, h3]
    ext x
    rcases hall x with rfl | rfl | rfl <;> simp [hd, h20, h21, h21.symm, hd.symm]
  let c0 := singletonCycle (d + d)
  let c : RainbowCycle ({0, d}ᶜ : Set G) :=
    ⟨c0.next, (congrArg (fun S : Set G => c0.next.IsCycleOn S) hA.symm).mp c0.cyclic,
      (congrArg (fun S : Set G => Set.InjOn (fun z => z + c0.next z) S) hA.symm).mp c0.rainbow⟩
  refine ⟨c, ?_⟩
  have hcolors : c.colors = c0.colors :=
    congrArg (fun S : Set G => (fun z => z + c0.next z) '' S) hA
  rw [hcolors, singleton_colors, hC]
  have h4 : (d + d) + (d + d) = d := by
    calc
      _ = (d + d + d) + d := by abel
      _ = d := by rw [h3, zero_add]
  rw [h4]

theorem normalized_of_generator (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    ∃ c : RainbowCycle ({0, d}ᶜ : Set G),
      c.colors = ({-d, d + d + d}ᶜ : Set G) := by
  by_cases h3 : d + d + d = 0
  · exact normalized_three hodd d hd hgen h3
  · exact ⟨twoGeneratorCycle hodd d hd h3 hgen,
      twoGeneratorCycle_colors hodd d hd h3 hgen⟩

end SunTwoDeletion
