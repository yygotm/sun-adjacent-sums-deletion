import SunTwoDeletion.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SunThreeDeletion
open SunTwoDeletion

theorem finRotate_isCycleOn {n : ℕ} (hn : 2 ≤ n) :
    (finRotate n).IsCycleOn (Set.univ : Set (Fin n)) := by
  have h := (isCycle_finRotate_of_le hn).isCycleOn
  have hs : {i : Fin n | finRotate n i ≠ i} = Set.univ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hi : i ∈ (finRotate n).support := by
      rw [support_finRotate_of_le hn]
      exact Finset.mem_univ i
    exact Equiv.Perm.mem_support.mp hi
  rwa [hs] at h

/-- Only kernel-checkable finite propositions are needed for an explicit witness. -/
theorem cycle_of_certificate {G : Type*} [AddCommGroup G]
    {n : ℕ} (hn : 2 ≤ n) (v : Fin n → G) (A : Set G)
    (hv : (List.ofFn v).Nodup)
    (hc : (List.ofFn (fun i => v i + v (finRotate n i))).Nodup)
    (hrange : ∀ x, x ∈ List.ofFn v ↔ x ∈ A) :
    HasRainbowCycle A := by
  let e : Fin n ↪ G := ⟨v, List.nodup_ofFn.mp hv⟩
  have he : Set.range e = A := by
    ext x
    change (∃ i, v i = x) ↔ x ∈ A
    simpa only [List.mem_ofFn] using hrange x
  have c := RainbowCycle.ofEmbedding (finRotate n) (finRotate_isCycleOn hn) e
    (List.nodup_ofFn.mp hc)
  rw [he] at c
  exact ⟨c⟩

theorem three_cycle_of_certificate {m n : ℕ} (hn : 2 ≤ n)
    (a b c : ZMod m) (v : Fin n → ZMod m)
    (hv : (List.ofFn v).Nodup)
    (hc : (List.ofFn (fun i => v i + v (finRotate n i))).Nodup)
    (hrange : ∀ x : ZMod m, x ∈ List.ofFn v ↔ x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    HasRainbowCycle ({a, b, c}ᶜ : Set (ZMod m)) := by
  apply cycle_of_certificate hn v _ hv hc
  intro x
  simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    using hrange x

end SunThreeDeletion

