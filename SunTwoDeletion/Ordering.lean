import SunTwoDeletion.Main
import SunTwoDeletion.Linearize

set_option autoImplicit false

namespace SunTwoDeletion

/-- The literal cyclic successor: increment the index and wrap the last index to zero. -/
def cyclicSuccessor {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, hn⟩

theorem cyclicSuccessor_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (cyclicSuccessor hn i).val = (i.val + 1) % n := by
  by_cases hi : i.val + 1 < n
  · simp [cyclicSuccessor, hi, Nat.mod_eq_of_lt hi]
  · have heq : i.val + 1 = n := by have := i.isLt; omega
    simp [cyclicSuccessor, hi, heq]

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem cycle_as_ordering (s : Finset G) (c : RainbowCycle (s : Set G))
    (u : G) (hu : u ∈ s) :
    ∃ (hn : 0 < s.card) (v : Fin s.card ↪ G),
      Set.range v = (s : Set G) ∧
      Function.Injective (fun i => v i + v (cyclicSuccessor hn i)) ∧
      Set.range (fun i => v i + v (cyclicSuccessor hn i)) = c.colors := by
  let hn : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  let v := cycleEmbedding c u hu
  have hv := cycleEmbedding_range c u hu
  have hnext : ∀ i, c.next (v i) = v (cyclicSuccessor hn i) := by
    intro i
    by_cases hi : i.val + 1 < s.card
    · rw [cyclicSuccessor, dif_pos hi]
      exact cycleEmbedding_next c u hu i hi
    · rw [cyclicSuccessor, dif_neg hi]
      exact (cycleEmbedding_last_next c u hu i hi).trans (cycleEmbedding_first c u hu).symm
  refine ⟨hn, v, hv, ?_, ?_⟩
  · intro i j heq
    apply v.injective
    apply c.rainbow (cycleEmbedding_mem c u hu i) (cycleEmbedding_mem c u hu j)
    change v i + c.next (v i) = v j + c.next (v j)
    rw [hnext i, hnext j]
    exact heq
  · ext z
    constructor
    · rintro ⟨i, heq⟩
      refine ⟨v i, cycleEmbedding_mem c u hu i, ?_⟩
      change v i + c.next (v i) = z
      rw [hnext]
      exact heq
    · rintro ⟨x, hx, heq⟩
      obtain ⟨i, rfl⟩ := hv.symm.subset hx
      refine ⟨i, ?_⟩
      change v i + c.next (v i) = z at heq
      rw [hnext] at heq
      exact heq

/-- An explicit indexed ordering with the exact set of adjacent sums. -/
theorem sun_two_deletion_ordering (G : Type*) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G - 2)
    (a b : G) (hab : a ≠ b) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G - 2 ∧ 2 < n ∧
      Set.range v = ({a, b}ᶜ : Set G) ∧
      Function.Injective (fun i => v i + v (cyclicSuccessor hn i)) ∧
      Set.range (fun i => v i + v (cyclicSuccessor hn i)) =
        ({3 • a - b, 3 • b - a}ᶜ : Set G) := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := sun_two_deletion_exact G hodd hsize a b hab
  let s : Finset G := ({a, b} : Finset G)ᶜ
  have hs : (s : Set G) = ({a, b}ᶜ : Set G) := by
    ext z
    simp [s, not_or, and_comm]
  have hcard : s.card = Nat.card G - 2 := by
    simp [s, Finset.card_compl, hab, Nat.card_eq_fintype_card]
    omega
  have hpos : 0 < s.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  let c' : RainbowCycle (s : Set G) :=
    ⟨c.next, (congrArg (fun S : Set G => c.next.IsCycleOn S) hs.symm).mp c.cyclic,
      (congrArg (fun S : Set G => Set.InjOn (fun z => z + c.next z) S) hs.symm).mp c.rainbow⟩
  have hc' : c'.colors = c.colors :=
    congrArg (fun S : Set G => (fun z => z + c.next z) '' S) hs
  obtain ⟨hn, v, hv, hinj, hcolors⟩ := cycle_as_ordering s c' u hu
  exact ⟨s.card, hn, v, hcard, by omega, hv.trans hs, hinj,
    hcolors.trans (hc'.trans hc)⟩

end SunTwoDeletion
