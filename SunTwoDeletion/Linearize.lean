import SunTwoDeletion.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] {s : Finset G}

def cycleEmbedding (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s) :
    Fin s.card ↪ G where
  toFun i := (c.next ^ i.val) u
  inj' := by
    intro i j h
    have hm := (c.cyclic.pow_apply_eq_pow_apply hu).mp h
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm

theorem cycleEmbedding_mem (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s)
    (i : Fin s.card) : cycleEmbedding c u hu i ∈ s :=
  c.cyclic.1.mapsTo.perm_pow i.val hu

theorem cycleEmbedding_range (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s) :
    Set.range (cycleEmbedding c u hu) = (s : Set G) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact cycleEmbedding_mem c u hu i
  · intro hx
    obtain ⟨i, hi, hix⟩ := c.cyclic.exists_pow_eq hu hx
    exact ⟨⟨i, hi⟩, hix⟩

theorem cycleEmbedding_first (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s) :
    cycleEmbedding c u hu ⟨0, Finset.card_pos.mpr ⟨u, hu⟩⟩ = u := by
  change (c.next ^ (0 : ℕ)) u = u
  simp

theorem cycleEmbedding_next (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s)
    (i : Fin s.card) (hi : i.val + 1 < s.card) :
    c.next (cycleEmbedding c u hu i) =
      cycleEmbedding c u hu ⟨i.val + 1, hi⟩ := by
  change c.next ((c.next ^ i.val) u) = (c.next ^ (i.val + 1)) u
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem cycleEmbedding_last_next (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s)
    (i : Fin s.card) (hi : ¬i.val + 1 < s.card) :
    c.next (cycleEmbedding c u hu i) = u := by
  have hcard : i.val + 1 = s.card := by have := i.isLt; omega
  change c.next ((c.next ^ i.val) u) = u
  rw [← Equiv.Perm.mul_apply, ← pow_succ', hcard]
  exact c.cyclic.pow_card_apply hu

theorem cycleEmbedding_last (c : RainbowCycle (s : Set G)) (u : G) (hu : u ∈ s)
    (v : G) (hv : c.next v = u) (i : Fin s.card) (hi : ¬i.val + 1 < s.card) :
    cycleEmbedding c u hu i = v := by
  apply c.next.injective
  exact (cycleEmbedding_last_next c u hu i hi).trans hv.symm

theorem cycleEmbedding_internal_injective (c : RainbowCycle (s : Set G))
    (u : G) (hu : u ∈ s) (i j : Fin s.card)
    (hi : i.val + 1 < s.card) (hj : j.val + 1 < s.card)
    (heq : cycleEmbedding c u hu i + cycleEmbedding c u hu ⟨i.val + 1, hi⟩ =
      cycleEmbedding c u hu j + cycleEmbedding c u hu ⟨j.val + 1, hj⟩) : i = j := by
  apply (cycleEmbedding c u hu).injective
  apply c.rainbow (cycleEmbedding_mem c u hu i) (cycleEmbedding_mem c u hu j)
  simpa only [cycleEmbedding_next c u hu i hi, cycleEmbedding_next c u hu j hj] using heq

theorem cycleEmbedding_avoid_closing (c : RainbowCycle (s : Set G))
    (u : G) (hu : u ∈ s) (v : G) (hv : c.next v = u) (hvs : v ∈ s)
    (i : Fin s.card) (hi : i.val + 1 < s.card) :
    cycleEmbedding c u hu i + cycleEmbedding c u hu ⟨i.val + 1, hi⟩ ≠ v + u := by
  intro heq
  have hiu : cycleEmbedding c u hu i = v := c.rainbow
    (cycleEmbedding_mem c u hu i) hvs (by
      simpa only [cycleEmbedding_next c u hu i hi, hv] using heq)
  have hsu : cycleEmbedding c u hu ⟨i.val + 1, hi⟩ = u := by
    rw [← cycleEmbedding_next, hiu, hv]
  have hz := (cycleEmbedding c u hu).injective
    (hsu.trans (cycleEmbedding_first c u hu).symm)
  have := congrArg Fin.val hz
  simp only at this
  omega

end SunTwoDeletion
