import SunTwoDeletion.Linearize

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

/-- A nonempty rainbow path, with its closing color reserved rather than used internally. -/
structure RainbowPath (A : Set G) (x y : G) where
  len : ℕ
  positive : 0 < len
  vertex : Fin len ↪ G
  range_vertex : Set.range vertex = A
  first : vertex ⟨0, positive⟩ = x
  last : ∀ j : Fin len, ¬j.val + 1 < len → vertex j = y
  internal_injective : ∀ (j k : Fin len) (hj : j.val + 1 < len) (hk : k.val + 1 < len),
    vertex j + vertex ⟨j.val + 1, hj⟩ = vertex k + vertex ⟨k.val + 1, hk⟩ → j = k
  internal_avoid : ∀ (j : Fin len) (hj : j.val + 1 < len),
    vertex j + vertex ⟨j.val + 1, hj⟩ ≠ x + y

noncomputable def RainbowPath.ofCycle {s : Finset G}
    (c : RainbowCycle (s : Set G)) (x y : G) (hx : x ∈ s) (hy : y ∈ s)
    (hclose : c.next y = x) : RainbowPath (s : Set G) x y where
  len := s.card
  positive := Finset.card_pos.mpr ⟨x, hx⟩
  vertex := cycleEmbedding c x hx
  range_vertex := cycleEmbedding_range c x hx
  first := cycleEmbedding_first c x hx
  last := fun j hj => cycleEmbedding_last c x hx y hclose j hj
  internal_injective := fun j k hj hk => cycleEmbedding_internal_injective c x hx j k hj hk
  internal_avoid := by
    intro j hj
    simpa only [add_comm x y] using cycleEmbedding_avoid_closing c x hx y hclose hy j hj

noncomputable def RainbowPath.ofFiniteCycle [Finite G] {A : Set G}
    (c : RainbowCycle A) (x y : G) (hx : x ∈ A) (hy : y ∈ A)
    (hclose : c.next y = x) : RainbowPath A x y := by
  classical
  letI := Fintype.ofFinite G
  let s := A.toFinset
  have hs : (s : Set G) = A := Set.coe_toFinset A
  let c' : RainbowCycle (s : Set G) :=
    ⟨c.next, by rw [hs]; exact c.cyclic, by rw [hs]; exact c.rainbow⟩
  have hc' : c'.next = c.next := rfl
  have p := RainbowPath.ofCycle c' x y (by simpa [s] using hx)
    (by simpa [s] using hy) (by rw [hc']; exact hclose)
  exact ⟨p.len, p.positive, p.vertex, p.range_vertex.trans hs, p.first, p.last,
    p.internal_injective, p.internal_avoid⟩

theorem RainbowPath.ofFiniteCycle_internal_next [Finite G] {A : Set G}
    (c : RainbowCycle A) (x y : G) (hx : x ∈ A) (hy : y ∈ A)
    (hclose : c.next y = x)
    (j : Fin (RainbowPath.ofFiniteCycle c x y hx hy hclose).len)
    (hj : j.val + 1 < (RainbowPath.ofFiniteCycle c x y hx hy hclose).len) :
    c.next ((RainbowPath.ofFiniteCycle c x y hx hy hclose).vertex j) =
      (RainbowPath.ofFiniteCycle c x y hx hy hclose).vertex ⟨j.val + 1, hj⟩ := by
  change c.next ((c.next ^ j.val) x) = (c.next ^ (j.val + 1)) x
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem RainbowPath.mem {A : Set G} {x y : G} (p : RainbowPath A x y) (j : Fin p.len) :
    p.vertex j ∈ A := by
  exact p.range_vertex.subset ⟨j, rfl⟩

theorem RainbowPath.full_internal_colors [Finite G] (x y : G)
    (p : RainbowPath (Set.univ : Set G) x y) :
    {z | ∃ (j : Fin p.len) (hj : j.val + 1 < p.len),
      p.vertex j + p.vertex ⟨j.val + 1, hj⟩ = z} = ({x + y}ᶜ : Set G) := by
  classical
  let f : Fin p.len → G := fun j =>
    if hj : j.val + 1 < p.len then p.vertex j + p.vertex ⟨j.val + 1, hj⟩ else x + y
  have hf : Function.Injective f := by
    intro j k h
    dsimp [f] at h
    split_ifs at h with hj hk hk
    · exact p.internal_injective j k hj hk h
    · exact (p.internal_avoid j hj h).elim
    · exact (p.internal_avoid k hk h.symm).elim
    · apply Fin.ext
      have := j.isLt
      have := k.isLt
      omega
  have hv : Function.Bijective p.vertex := ⟨p.vertex.injective,
    Set.range_eq_univ.mp p.range_vertex⟩
  let e : Fin p.len ≃ G := Equiv.ofBijective p.vertex hv
  have hs : Function.Surjective f := by
    have hinj : Function.Injective (f ∘ e.symm) := hf.comp e.symm.injective
    have := Finite.surjective_of_injective hinj
    intro z
    obtain ⟨w, hw⟩ := this z
    exact ⟨e.symm w, hw⟩
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact p.internal_avoid j hj
  · intro hz
    obtain ⟨j, hj⟩ := hs z
    dsimp [f] at hj
    split_ifs at hj with h
    · exact ⟨j, h, hj⟩
    · exact (hz hj.symm).elim

end SunTwoDeletion
