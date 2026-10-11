import SunTwoDeletion.Basic

set_option autoImplicit false

namespace SunTwoDeletion

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]

noncomputable def RainbowCycle.map {A : Set G} (c : RainbowCycle A)
    (f : G →+ K) (hf : Function.Injective f) : RainbowCycle (f '' A) := by
  classical
  let v : G ↪ K := ⟨f, hf⟩
  refine ⟨c.next.viaEmbedding v, ?_, ?_⟩
  · exact c.cyclic.extendDomain (Equiv.ofInjective v v.injective)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ heq
    change f x + (c.next.viaEmbedding v) (v x) =
      f y + (c.next.viaEmbedding v) (v y) at heq
    rw [c.next.viaEmbedding_apply, c.next.viaEmbedding_apply] at heq
    have hxy : x + c.next x = y + c.next y := by
      apply hf
      rw [map_add, map_add]
      exact heq
    exact congrArg f (c.rainbow hx hy hxy)

theorem RainbowCycle.map_next {A : Set G} (c : RainbowCycle A)
    (f : G →+ K) (hf : Function.Injective f) (x : G) :
    (c.map f hf).next (f x) = f (c.next x) :=
  c.next.viaEmbedding_apply ⟨f, hf⟩ x

theorem RainbowCycle.map_colors {A : Set G} (c : RainbowCycle A)
    (f : G →+ K) (hf : Function.Injective f) :
    (c.map f hf).colors = f '' c.colors := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, heq⟩
    refine ⟨x + c.next x, ⟨x, hx, rfl⟩, ?_⟩
    change f x + (c.map f hf).next (f x) = z at heq
    rw [c.map_next f hf x, ← map_add] at heq
    exact heq
  · rintro ⟨_, ⟨x, hx, rfl⟩, heq⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    change f x + (c.map f hf).next (f x) = z
    rw [c.map_next f hf x, ← map_add]
    exact heq

theorem edge_property_of_zero
    (h : ∀ d : G, d ≠ 0 → ∃ c : RainbowCycle (Set.univ : Set G), c.next 0 = d) :
    EdgeProperty G := by
  intro u v huv
  obtain ⟨c, hc⟩ := h (v - u) (sub_ne_zero.mpr huv.symm)
  let t := c.translate u
  have hset : (fun x : G => x + u) '' Set.univ = Set.univ :=
    Set.image_univ.trans (Set.range_eq_univ.mpr (Equiv.addRight u).surjective)
  let C : RainbowCycle (Set.univ : Set G) :=
    ⟨t.next, (congrArg (fun S : Set G => t.next.IsCycleOn S) hset).mp t.cyclic,
      (congrArg (fun S : Set G => Set.InjOn (fun x => x + t.next x) S) hset).mp t.rainbow⟩
  refine ⟨C, ?_⟩
  change t.next u = v
  have hh := c.translate_next u 0
  simpa only [zero_add, hc, sub_add_cancel] using hh

theorem full_cycle_of_edge_property (hE : EdgeProperty G) :
    HasRainbowCycle (Set.univ : Set G) := by
  classical
  by_cases h : ∃ d : G, d ≠ 0
  · obtain ⟨d, hd⟩ := h
    obtain ⟨c, _⟩ := hE 0 d hd.symm
    exact ⟨c⟩
  · have hu : ({0} : Set G) = Set.univ := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
      by_contra hx
      exact h ⟨x, hx⟩
    exact ⟨hu ▸ singletonCycle (0 : G)⟩

end SunTwoDeletion
