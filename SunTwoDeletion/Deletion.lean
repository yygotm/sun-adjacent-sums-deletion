import SunTwoDeletion.Cyclic
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace SunTwoDeletion

open Equiv
open scoped Classical

variable {G : Type*} [AddCommGroup G]

noncomputable def skipTwo (d : G) : Perm G := by
  classical
  exact Equiv.swap d (d + d) * (Equiv.swap 0 d * Equiv.addRight d)

theorem skipTwo_apply (d x : G) (hx0 : x ≠ 0) (hxd : x ≠ d) :
    skipTwo d x = if x = -d then d + d else x + d := by
  classical
  by_cases hx : x = -d
  · subst x
    simp [skipTwo]
  · have h0 : x + d ≠ 0 := by
      intro h
      apply hx
      exact eq_neg_of_add_eq_zero_left h
    have h1 : x + d ≠ d := by simpa using hx0
    have h2 : x + d ≠ d + d := by simpa using hxd
    simp [skipTwo, Equiv.swap_apply_of_ne_of_ne h0 h1,
      Equiv.swap_apply_of_ne_of_ne h1 h2, hx]

theorem skipTwo_fixed_iff (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (h3 : d + d + d ≠ 0) (x : G) :
    skipTwo d x = x ↔ x = 0 ∨ x = d := by
  classical
  have h20 : d + d ≠ 0 := by
    intro h
    exact hd (double_injective hodd (by simpa using h))
  have h21 : d + d ≠ d := by simpa using hd
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    by_cases hxd : x = d
    · exact Or.inr hxd
    rw [skipTwo_apply d x hx0 hxd] at hx
    split_ifs at hx with hn
    · exfalso
      apply h3
      rw [hn] at hx
      rw [hx]
      simp
    · exfalso
      exact hd (by simpa using hx)
  · rintro (rfl | rfl)
    · simp [skipTwo, Equiv.swap_apply_def, hd, h20, h21, hd.symm, h20.symm]
    · simp [skipTwo, Equiv.swap_apply_def, hd, h20, h21]

theorem skipTwo_color (d x : G) (hx0 : x ≠ 0) (hxd : x ≠ d) :
    x + skipTwo d x = if x = -d then d else (x + x) + d := by
  rw [skipTwo_apply d x hx0 hxd]
  by_cases hx : x = -d
  · subst x
    simp
  · simp only [if_neg hx]
    abel

theorem skipTwo_cyclic (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0)
    (h3 : d + d + d ≠ 0) (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    (skipTwo d).IsCycleOn ({0, d}ᶜ : Set G) := by
  classical
  have h20 : d + d ≠ 0 := by
    intro h
    exact hd (double_injective hodd (by simpa using h))
  have h21 : d + d ≠ d := by simpa using hd
  have h31 : d + d + d ≠ d := by simpa using h20
  have hf : (Equiv.addRight d).IsCycle := by
    apply Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
    refine ⟨Set.univ, ⟨0, Set.mem_univ _, d, Set.mem_univ _, hd.symm⟩,
      (generatorCycle hodd d hgen).cyclic, ?_⟩
    intro x _
    exact Set.mem_univ x
  have hfirst : (Equiv.swap 0 d * Equiv.addRight d).IsCycle := by
    simpa using hf.swap_mul (x := 0) (by simpa using hd) (by simpa using h20)
  have hnext : (Equiv.swap 0 d * Equiv.addRight d) d = d + d := by
    simp [Equiv.swap_apply_of_ne_of_ne h20 h21]
  have hnextnext : (Equiv.swap 0 d * Equiv.addRight d) (d + d) = d + d + d := by
    simp [Equiv.swap_apply_of_ne_of_ne h3 h31]
  have hsecond : (skipTwo d).IsCycle := by
    have hh := hfirst.swap_mul (x := d) (by rw [hnext]; exact h21)
      (by rw [hnext, hnextnext]; exact h31)
    simpa only [hnext, skipTwo] using hh
  convert hsecond.isCycleOn using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, ne_eq, skipTwo_fixed_iff hodd d hd h3]

noncomputable def twoGeneratorCycle (hodd : Odd (Nat.card G)) (d : G)
    (hd : d ≠ 0) (h3 : d + d + d ≠ 0)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    RainbowCycle ({0, d}ᶜ : Set G) := by
  classical
  refine ⟨skipTwo d, skipTwo_cyclic hodd d hd h3 hgen, ?_⟩
  intro x hx y hy h
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hxd : x ≠ d := fun h => hx (by simp [h])
  have hy0 : y ≠ 0 := fun h => hy (by simp [h])
  have hyd : y ≠ d := fun h => hy (by simp [h])
  change x + skipTwo d x = y + skipTwo d y at h
  rw [skipTwo_apply d x hx0 hxd, skipTwo_apply d y hy0 hyd] at h
  split_ifs at h with hxneg hyneg hyneg
  · exact hxneg.trans hyneg.symm
  · exfalso
    apply hy0
    apply double_injective hodd
    subst x
    have : d = (y + y) + d := by
      calc
        d = -d + (d + d) := by abel
        _ = y + (y + d) := h
        _ = (y + y) + d := by abel
    simpa using this.symm
  · exfalso
    apply hx0
    apply double_injective hodd
    subst y
    have : (x + x) + d = d := by
      calc
        (x + x) + d = x + (x + d) := by abel
        _ = -d + (d + d) := h
        _ = d := by abel
    simpa using this
  · apply double_injective hodd
    simpa only [← add_assoc, add_left_inj] using h

theorem twoGeneratorCycle_colors (hodd : Odd (Nat.card G)) (d : G)
    (hd : d ≠ 0) (h3 : d + d + d ≠ 0)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    (twoGeneratorCycle hodd d hd h3 hgen).colors =
      ({-d, d + d + d}ᶜ : Set G) := by
  have h20 : d + d ≠ 0 := by
    intro h
    exact hd (double_injective hodd (by simpa using h))
  have hdn : d ≠ -d := by
    intro h
    apply h20
    calc
      d + d = -d + d := congrArg (· + d) h
      _ = 0 := neg_add_cancel d
  have hd3 : d ≠ d + d + d := by
    intro h
    exact h20 (by simpa using h.symm)
  ext z
  change (∃ x ∈ ({0, d}ᶜ : Set G), x + skipTwo d x = z) ↔
    z ∉ ({-d, d + d + d} : Set G)
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hx (by simp [h])
    have hxd : x ≠ d := fun h => hx (by simp [h])
    rw [skipTwo_color d x hx0 hxd]
    by_cases hn : x = -d
    · simpa only [if_pos hn, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
        And.intro hdn hd3
    · simp only [if_neg hn, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro heq
        apply hn
        apply double_injective hodd
        apply add_right_cancel (b := d)
        calc
          (x + x) + d = -d := heq
          _ = (-d + -d) + d := by abel
      · intro heq
        exact hxd (double_injective hodd (add_right_cancel heq))
  · intro hz
    have hzneg : z ≠ -d := fun h => hz (by simp [h])
    have hz3 : z ≠ d + d + d := fun h => hz (by simp [h])
    by_cases hzd : z = d
    · subst z
      refine ⟨-d, ?_, ?_⟩
      · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨neg_ne_zero.mpr hd, hdn.symm⟩
      · rw [skipTwo_color d (-d) (neg_ne_zero.mpr hd) hdn.symm]
        simp
    · obtain ⟨x, hx⟩ := double_surjective hodd (z - d)
      change x + x = z - d at hx
      have hsum : (x + x) + d = z := by rw [hx]; abel
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        apply hzd
        simpa using hsum.symm
      have hxd : x ≠ d := by
        intro h
        subst x
        exact hz3 hsum.symm
      have hxn : x ≠ -d := by
        intro h
        subst x
        apply hzneg
        calc
          z = (-d + -d) + d := hsum.symm
          _ = -d := by abel
      refine ⟨x, ?_, ?_⟩
      · simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using And.intro hx0 hxd
      · rw [skipTwo_color d x hx0 hxd, if_neg hxn]
        exact hsum

theorem generator_three_nonzero (d : G)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples d) (hcard : 3 < Nat.card G) :
    d + d + d ≠ 0 := by
  intro h
  have hs : (3 : ℕ) • d = 0 := by simpa only [succ_nsmul, zero_nsmul, zero_add] using h
  have hv := addOrderOf_dvd_of_nsmul_eq_zero hs
  rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen] at hv
  have := Nat.le_of_dvd (by decide : 0 < 3) hv
  omega

end SunTwoDeletion
