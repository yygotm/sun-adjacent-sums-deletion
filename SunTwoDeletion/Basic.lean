import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace SunTwoDeletion

open Equiv

variable {G : Type*} [AddCommGroup G]

/-- A single cycle through precisely A; the singleton case reserves its doubled color. -/
structure RainbowCycle (A : Set G) where
  next : Perm G
  cyclic : next.IsCycleOn A
  rainbow : Set.InjOn (fun x => x + next x) A

def RainbowCycle.colors {A : Set G} (c : RainbowCycle A) : Set G :=
  (fun x => x + c.next x) '' A

def HasRainbowCycle (A : Set G) : Prop := Nonempty (RainbowCycle A)

def EdgeProperty (G : Type*) [AddCommGroup G] : Prop :=
  ∀ u v : G, u ≠ v → ∃ c : RainbowCycle (Set.univ : Set G), c.next u = v

def TwoDeletionStatement (G : Type*) [AddCommGroup G] [Finite G] : Prop :=
  Odd (Nat.card G) → 2 < Nat.card G - 2 →
  ∀ a b : G, a ≠ b → HasRainbowCycle ({a, b}ᶜ : Set G)

def ExactTwoDeletionStatement (G : Type*) [AddCommGroup G] [Finite G] : Prop :=
  Odd (Nat.card G) → 2 < Nat.card G - 2 →
  ∀ a b : G, a ≠ b →
    ∃ c : RainbowCycle ({a, b}ᶜ : Set G),
      c.colors = ({3 • a - b, 3 • b - a}ᶜ : Set G)

def singletonCycle (u : G) : RainbowCycle ({u} : Set G) where
  next := 1
  cyclic := by simp
  rainbow := by
    intro x hx y hy _
    simpa using (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm

theorem singleton_colors (u : G) :
    (singletonCycle u).colors = {u + u} := by
  simp [RainbowCycle.colors, singletonCycle]

theorem RainbowCycle.full_colors [Finite G] (c : RainbowCycle (Set.univ : Set G)) :
    c.colors = Set.univ := by
  have hi : Function.Injective (fun x => x + c.next x) :=
    fun x y h => c.rainbow (Set.mem_univ x) (Set.mem_univ y) h
  simpa [RainbowCycle.colors] using
    Set.range_eq_univ.mpr (Finite.surjective_of_injective hi)

/-- Change of coordinates by translation; conjugation retains the single-cycle condition. -/
def RainbowCycle.translate {A : Set G} (c : RainbowCycle A) (t : G) :
    RainbowCycle ((fun x => x + t) '' A) where
  next := (Equiv.addRight t) * c.next * (Equiv.addRight t)⁻¹
  cyclic := c.cyclic.conj
  rainbow := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    have hsum : x + c.next x = y + c.next y := by
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
        Equiv.coe_addRight, Equiv.addRight_symm_apply, add_neg_cancel_right] at h
      apply add_right_cancel (b := t + t)
      calc
        (x + c.next x) + (t + t) = (x + t) + (c.next x + t) := by abel
        _ = (y + t) + (c.next y + t) := h
        _ = (y + c.next y) + (t + t) := by abel
    exact congrArg (· + t) (c.rainbow hx hy hsum)

theorem RainbowCycle.translate_next {A : Set G} (c : RainbowCycle A) (t x : G) :
    (c.translate t).next (x + t) = c.next x + t := by
  simp [RainbowCycle.translate, Equiv.Perm.mul_apply]

theorem RainbowCycle.translate_colors {A : Set G} (c : RainbowCycle A) (t : G) :
    (c.translate t).colors = (fun s => s + (t + t)) '' c.colors := by
  ext z
  simp only [RainbowCycle.colors, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨x + c.next x, ⟨x, hx, rfl⟩, ?_⟩
    rw [c.translate_next] at hz
    simpa only [add_assoc, add_left_comm, add_comm] using hz
  · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨x + t, ⟨x, hx, rfl⟩, ?_⟩
    rw [c.translate_next]
    simpa only [add_assoc, add_left_comm, add_comm] using hz

theorem translate_compl_pair (a b t : G) :
    (fun x => x + t) '' ({a, b}ᶜ : Set G) = ({a + t, b + t}ᶜ : Set G) := by
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [add_left_inj] using hy
  · intro hx
    refine ⟨x - t, ?_, sub_add_cancel x t⟩
    simpa only [sub_eq_iff_eq_add] using hx

theorem exact_implies_two_deletion [Finite G] (h : ExactTwoDeletionStatement G) :
    TwoDeletionStatement G := by
  intro ho hn a b hab
  obtain ⟨c, _⟩ := h ho hn a b hab
  exact ⟨c⟩

noncomputable def RainbowCycle.ofEmbedding {J : Type*} (p : Perm J)
    (hp : p.IsCycleOn Set.univ) (v : J ↪ G)
    (hc : Function.Injective (fun j => v j + v (p j))) :
    RainbowCycle (Set.range v) := by
  classical
  refine ⟨p.viaEmbedding v, ?_, ?_⟩
  · change (p.extendDomain (Equiv.ofInjective v v.injective)).IsCycleOn _
    convert hp.extendDomain (Equiv.ofInjective v v.injective) using 1
    exact Set.image_univ.symm
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    change v x + (p.viaEmbedding v) (v x) = v y + (p.viaEmbedding v) (v y) at heq
    rw [p.viaEmbedding_apply, p.viaEmbedding_apply] at heq
    exact congrArg v (hc heq)

theorem RainbowCycle.ofEmbedding_next {J : Type*} (p : Perm J)
    (hp : p.IsCycleOn Set.univ) (v : J ↪ G)
    (hc : Function.Injective (fun j => v j + v (p j))) (j : J) :
    (RainbowCycle.ofEmbedding p hp v hc).next (v j) = v (p j) :=
  p.viaEmbedding_apply v j

theorem RainbowCycle.ofEmbedding_colors {J : Type*} (p : Perm J)
    (hp : p.IsCycleOn Set.univ) (v : J ↪ G)
    (hc : Function.Injective (fun j => v j + v (p j))) :
    (RainbowCycle.ofEmbedding p hp v hc).colors =
      Set.range (fun j => v j + v (p j)) := by
  ext z
  simp only [RainbowCycle.colors, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hz⟩
    exact ⟨j, by simpa only [RainbowCycle.ofEmbedding_next] using hz⟩
  · rintro ⟨j, hz⟩
    exact ⟨v j, ⟨j, rfl⟩, by simpa only [RainbowCycle.ofEmbedding_next] using hz⟩

end SunTwoDeletion
