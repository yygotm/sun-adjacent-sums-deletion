import SunTwoDeletion.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace SunTwoDeletion

open Equiv

variable {I : Type*} (len : I → ℕ) (hpos : ∀ i, 0 < len i) (σ : Perm I)

/-- Consecutive positions in each nonempty block, followed by the next block. -/
def blockNext : (Σ i, Fin (len i)) → (Σ i, Fin (len i)) :=
  fun ⟨i, j⟩ =>
    if h : j.val + 1 < len i then ⟨i, ⟨j.val + 1, h⟩⟩
    else ⟨σ i, ⟨0, hpos (σ i)⟩⟩

theorem blockNext_injective : Function.Injective (blockNext len hpos σ) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ heq
  simp only [blockNext] at heq
  split_ifs at heq with hj hl hl
  · have hik : i = k := congrArg Sigma.fst heq
    subst k
    have hval : j.val + 1 = l.val + 1 := by
      simpa using congrArg (fun x : Σ i, Fin (len i) => x.2.val) heq
    have : j = l := Fin.ext (by omega)
    subst l
    rfl
  · have hval : j.val + 1 = 0 := by
      simpa using congrArg (fun x : Σ i, Fin (len i) => x.2.val) heq
    omega
  · have hval : 0 = l.val + 1 := by
      simpa using congrArg (fun x : Σ i, Fin (len i) => x.2.val) heq
    omega
  · have hik : i = k := σ.injective (congrArg Sigma.fst heq)
    subst k
    have : j = l := Fin.ext (by have := j.isLt; have := l.isLt; omega)
    subst l
    rfl

noncomputable def blockPerm [Finite I] : Perm (Σ i, Fin (len i)) :=
  Equiv.ofBijective (blockNext len hpos σ)
    ⟨blockNext_injective len hpos σ,
      Finite.surjective_of_injective (blockNext_injective len hpos σ)⟩

@[simp] theorem blockPerm_apply [Finite I] (x : Σ i, Fin (len i)) :
    blockPerm len hpos σ x = blockNext len hpos σ x := rfl

theorem block_sameCycle [Finite I] (i : I) (j : Fin (len i)) :
    (blockPerm len hpos σ).SameCycle ⟨i, ⟨0, hpos i⟩⟩ ⟨i, j⟩ := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ j ih =>
    have hj' : j < len i := by omega
    have hprev := ih hj'
    have hnext : blockPerm len hpos σ ⟨i, ⟨j, hj'⟩⟩ =
        (⟨i, ⟨j + 1, hj⟩⟩ : Σ i, Fin (len i)) := by
      simp [blockNext, hj]
    exact hnext ▸ hprev.apply_right

theorem block_bridge [Finite I] (i : I) :
    (blockPerm len hpos σ).SameCycle
      ⟨i, ⟨0, hpos i⟩⟩ ⟨σ i, ⟨0, hpos (σ i)⟩⟩ := by
  have hi := hpos i
  let last : Fin (len i) := ⟨len i - 1, by omega⟩
  have h := block_sameCycle len hpos σ i last
  have hn : blockPerm len hpos σ ⟨i, last⟩ =
      (⟨σ i, ⟨0, hpos (σ i)⟩⟩ : Σ i, Fin (len i)) := by
    simp [blockNext, last, show ¬(len i - 1 + 1 < len i) by omega]
  exact hn ▸ h.apply_right

theorem blockPerm_cyclic [Finite I] (hσ : σ.IsCycleOn Set.univ) :
    (blockPerm len hpos σ).IsCycleOn Set.univ := by
  refine ⟨(blockPerm len hpos σ).bijective.bijOn_univ, ?_⟩
  rintro ⟨i, j⟩ _ ⟨k, l⟩ _
  obtain ⟨n, hn⟩ := (hσ.2 (Set.mem_univ i) (Set.mem_univ k)).exists_nat_pow_eq
  have reach : ∀ n : ℕ, (blockPerm len hpos σ).SameCycle
      ⟨i, ⟨0, hpos i⟩⟩ ⟨(σ ^ n) i, ⟨0, hpos ((σ ^ n) i)⟩⟩ := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      have hb := block_bridge len hpos σ ((σ ^ n) i)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans hb
  have hr := reach n
  rw [hn] at hr
  exact (block_sameCycle len hpos σ i j).symm.trans
    (hr.trans (block_sameCycle len hpos σ k l))

end SunTwoDeletion
