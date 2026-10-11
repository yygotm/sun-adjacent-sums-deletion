import SunTwoDeletion.Blocks

set_option autoImplicit false

namespace SunTwoDeletion

open Equiv

/-- Precisely the local conditions needed for joining nonempty rainbow paths. -/
structure BlockData (I G : Type*) [AddCommGroup G] where
  len : I → ℕ
  positive : ∀ i, 0 < len i
  order : Perm I
  order_cyclic : order.IsCycleOn Set.univ
  reservationOrder : Perm I
  vertex : (Σ i, Fin (len i)) ↪ G
  label : G → I
  reserved : I → G
  reserved_label : ∀ i, label (reserved i) = i
  internal_label : ∀ i (j : Fin (len i)) (h : j.val + 1 < len i),
    label (vertex ⟨i, j⟩ + vertex ⟨i, ⟨j.val + 1, h⟩⟩) = i
  internal_avoid : ∀ i (j : Fin (len i)) (h : j.val + 1 < len i),
    vertex ⟨i, j⟩ + vertex ⟨i, ⟨j.val + 1, h⟩⟩ ≠ reserved i
  internal_injective : ∀ i (j k : Fin (len i))
    (hj : j.val + 1 < len i) (hk : k.val + 1 < len i),
    vertex ⟨i, j⟩ + vertex ⟨i, ⟨j.val + 1, hj⟩⟩ =
    vertex ⟨i, k⟩ + vertex ⟨i, ⟨k.val + 1, hk⟩⟩ → j = k
  boundary : ∀ i (j : Fin (len i)), ¬j.val + 1 < len i →
    vertex ⟨i, j⟩ + vertex ⟨order i, ⟨0, positive (order i)⟩⟩ =
      reserved (reservationOrder i)

namespace BlockData

variable {I G : Type*} [Finite I] [AddCommGroup G] (D : BlockData I G)

noncomputable def next : Perm (Σ i, Fin (D.len i)) :=
  blockPerm D.len D.positive D.order

noncomputable def color (x : Σ i, Fin (D.len i)) : G :=
  D.vertex x + D.vertex (D.next x)

theorem color_internal (i : I) (j : Fin (D.len i)) (hj : j.val + 1 < D.len i) :
    D.color ⟨i, j⟩ = D.vertex ⟨i, j⟩ + D.vertex ⟨i, ⟨j.val + 1, hj⟩⟩ := by
  simp [color, next, blockNext, hj]

theorem color_boundary (i : I) (j : Fin (D.len i)) (hj : ¬j.val + 1 < D.len i) :
    D.color ⟨i, j⟩ = D.reserved (D.reservationOrder i) := by
  simpa [color, next, blockNext, hj] using D.boundary i j hj

theorem color_injective : Function.Injective D.color := by
  rintro ⟨i, j⟩ ⟨k, l⟩ heq
  by_cases hj : j.val + 1 < D.len i
  · by_cases hl : l.val + 1 < D.len k
    · rw [D.color_internal i j hj, D.color_internal k l hl] at heq
      have hik : i = k := by
        have hh := congrArg D.label heq
        simpa only [D.internal_label] using hh
      subst k
      have h := D.internal_injective i j l hj hl heq
      subst l
      rfl
    · rw [D.color_internal i j hj, D.color_boundary k l hl] at heq
      have hik : i = D.reservationOrder k := by
        have hh := congrArg D.label heq
        simpa only [D.internal_label, D.reserved_label] using hh
      rw [← hik] at heq
      exact (D.internal_avoid i j hj heq).elim
  · by_cases hl : l.val + 1 < D.len k
    · rw [D.color_boundary i j hj, D.color_internal k l hl] at heq
      have hki : k = D.reservationOrder i := by
        have hh := congrArg D.label heq.symm
        simpa only [D.internal_label, D.reserved_label] using hh
      rw [← hki] at heq
      exact (D.internal_avoid k l hl heq.symm).elim
    · rw [D.color_boundary i j hj, D.color_boundary k l hl] at heq
      have hik : i = k := D.reservationOrder.injective (by
        have hh := congrArg D.label heq
        simpa only [D.reserved_label] using hh)
      subst k
      have h : j = l := Fin.ext (by have := j.isLt; have := l.isLt; omega)
      subst l
      rfl

noncomputable def assemble : RainbowCycle (Set.range D.vertex) :=
  RainbowCycle.ofEmbedding D.next
    (blockPerm_cyclic D.len D.positive D.order D.order_cyclic)
    D.vertex D.color_injective

theorem assemble_next (x : Σ i, Fin (D.len i)) :
    D.assemble.next (D.vertex x) = D.vertex (D.next x) :=
  RainbowCycle.ofEmbedding_next _ _ _ _ x

theorem assemble_colors :
    D.assemble.colors = Set.range D.color :=
  RainbowCycle.ofEmbedding_colors _ _ _ _

theorem reserved_present (i : I) : D.reserved i ∈ D.assemble.colors := by
  rw [D.assemble_colors]
  let k := D.reservationOrder.symm i
  have hk := D.positive k
  let j : Fin (D.len k) := ⟨D.len k - 1, by omega⟩
  refine ⟨⟨k, j⟩, ?_⟩
  rw [D.color_boundary k j (by dsimp [j]; omega)]
  simp [k]

end BlockData
end SunTwoDeletion
