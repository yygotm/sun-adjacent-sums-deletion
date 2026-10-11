import SunTwoDeletion.EdgeProperty
import SunTwoDeletion.ExactColors

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem normalized_missing_ne (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0) :
    -d ≠ d + d + d := by
  have h3 : (3 : ℕ) • d = d + d + d := by abel
  simpa only [nsmul_zero, zero_sub, sub_zero, h3] using
    (missing_colors_ne hodd (a := 0) (b := d) hd.symm)

theorem subgroup_deleted_set (H : AddSubgroup G) (d : G) (hdH : d ∈ H) :
    (H : Set G)ᶜ ∪ H.subtype '' ({0, (⟨d, hdH⟩ : H)}ᶜ : Set H) =
      ({0, d}ᶜ : Set G) := by
  ext z
  constructor
  · rintro (hz | ⟨x, hx, rfl⟩)
    · have h0 : z ≠ 0 := fun h => hz (h ▸ H.zero_mem)
      have hd : z ≠ d := fun h => hz (h ▸ hdH)
      simpa using And.intro h0 hd
    · have h0 : (x : G) ≠ 0 := by
        intro h
        exact hx (by left; exact Subtype.ext h)
      have hd : (x : G) ≠ d := by
        intro h
        exact hx (by right; exact Subtype.ext h)
      simpa using And.intro h0 hd
  · intro hz
    by_cases hzH : z ∈ H
    · right
      refine ⟨⟨z, hzH⟩, ?_, rfl⟩
      intro hx
      rcases hx with h | h
      · exact hz (Or.inl (congrArg (fun x : H => (x : G)) h))
      · exact hz (Or.inr (congrArg (fun x : H => (x : G)) h))
    · exact Or.inl hzH

/-- Lift exact two-deletion through a cyclic quotient; a singleton subgroup
cycle is permitted and is handled by the same gluing construction. -/
theorem lift_normalized_deletion (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (hq : 3 ≤ Nat.card (G ⧸ H)) (r : G)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (d : G) (hd : d ≠ 0) (hdH : d ∈ H)
    (cH : RainbowCycle ({0, (⟨d, hdH⟩ : H)}ᶜ : Set H))
    (hcolorsH : cH.colors =
      ({-(⟨d, hdH⟩ : H), (⟨d, hdH⟩ : H) + ⟨d, hdH⟩ + ⟨d, hdH⟩}ᶜ : Set H)) :
    ∃ c : RainbowCycle ({0, d}ᶜ : Set G),
      c.colors = ({-d, d + d + d}ᶜ : Set G) := by
  let dH : H := ⟨d, hdH⟩
  let A := H.subtype '' ({0, dH}ᶜ : Set H)
  let c0 := cH.map H.subtype Subtype.val_injective
  have hA : A ⊆ (H : Set G) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have h20 : d + d ≠ 0 := fun h => hd (double_injective hodd (by simpa using h))
  have h21 : d + d ≠ d := by simpa using hd
  have hv : d + d ∈ A := by
    refine ⟨dH + dH, ?_, rfl⟩
    have h0 : dH + dH ≠ 0 := fun h => h20 (congrArg (fun x : H => (x : G)) h)
    have h1 : dH + dH ≠ dH := fun h => h21 (congrArg (fun x : H => (x : G)) h)
    simpa using And.intro h0 h1
  let u := c0.next (d + d)
  have hu : u ∈ A := c0.cyclic.1.mapsTo hv
  obtain ⟨C, _, hcontrol⟩ := cyclic_quotient_glue_controlled hodd H hH hq
    (edge_property_odd H (subgroup_odd hodd H)) r hgen A hA c0
    u (d + d) hu hv rfl
  have hset : (H : Set G)ᶜ ∪ A = ({0, d}ᶜ : Set G) := subgroup_deleted_set H d hdH
  let c : RainbowCycle ({0, d}ᶜ : Set G) :=
    ⟨C.next, (congrArg (fun S : Set G => C.next.IsCycleOn S) hset).mp C.cyclic,
      (congrArg (fun S : Set G => Set.InjOn (fun z => z + C.next z) S) hset).mp C.rainbow⟩
  have hc : c.colors = C.colors :=
    congrArg (fun S : Set G => (fun z => z + C.next z) '' S) hset.symm
  have hnot {z : H} (hz : z ∉ cH.colors) : (z : G) ∉ c0.colors := by
    have hmap : c0.colors = H.subtype '' cH.colors :=
      cH.map_colors H.subtype Subtype.val_injective
    rw [hmap]
    rintro ⟨w, hw, heq⟩
    exact hz (Subtype.ext heq ▸ hw)
  have hneg : -d ∉ c.colors := by
    rw [hc]
    intro hz
    have hh := hcontrol (-d) hz (H.neg_mem hdH)
    apply hnot (z := -dH) ?_ hh
    rw [hcolorsH]
    exact fun h => h (Or.inl rfl)
  have hthree : d + d + d ∉ c.colors := by
    rw [hc]
    intro hz
    have hh := hcontrol (d + d + d) hz (H.add_mem (H.add_mem hdH hdH) hdH)
    apply hnot (z := dH + dH + dH) ?_ hh
    rw [hcolorsH]
    exact fun h => h (Or.inr rfl)
  exact ⟨c, exact_colors_of_two_forbidden 0 d (-d) (d + d + d) hd.symm
    (normalized_missing_ne hodd d hd) c hneg hthree⟩

end SunTwoDeletion
