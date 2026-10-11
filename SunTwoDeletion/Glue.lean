import SunTwoDeletion.QuotientAssembly
import SunTwoDeletion.Endpoints

set_option autoImplicit false

namespace SunTwoDeletion

open scoped Classical

variable {G : Type*} [AddCommGroup G] [Finite G]

noncomputable def pathsFromEndpoints (H : AddSubgroup G) (hE : EdgeProperty H)
    (r u v : G) (E : ClosedCosetEndpoints H r u v) (A : Set G)
    (hA : A ⊆ (H : Set G)) (p0 : RainbowPath A u v) : CosetPaths H r where
  A i := if i = 0 then A else {z | (QuotientAddGroup.mk z : G ⧸ H) = i}
  x := E.x
  y := E.y
  hx := E.hx
  hy := E.hy
  recurrence := E.recurrence
  path i := by
    classical
    by_cases hi : i = 0
    · subst i
      refine ⟨p0.len, p0.positive, p0.vertex, ?_,
        p0.first.trans E.x_zero.symm, ?_, p0.internal_injective, ?_⟩
      · simpa only [ite_true] using p0.range_vertex
      · intro j hj
        exact (p0.last j hj).trans E.y_zero.symm
      · intro j hj
        rw [E.x_zero, E.y_zero]
        exact p0.internal_avoid j hj
    · rw [if_neg hi]
      have he : (QuotientAddGroup.mk (E.x i) : G ⧸ H) = QuotientAddGroup.mk (E.y i) :=
        (E.hx i).trans (E.hy i).symm
      have p := Classical.choice (coset_path_exists H hE (E.x i) (E.y i) (E.distinct i hi) he)
      rw [E.hx i] at p
      exact p
  coset := by
    intro i z hz
    by_cases hi : i = 0
    · subst i
      simp only [ite_true] at hz
      exact (QuotientAddGroup.eq_zero_iff z).mpr (hA hz)
    · simpa only [if_neg hi, Set.mem_setOf_eq] using hz

theorem pathsFromEndpoints_union (H : AddSubgroup G) (hE : EdgeProperty H)
    (r u v : G) (E : ClosedCosetEndpoints H r u v) (A : Set G)
    (hA : A ⊆ (H : Set G)) (p0 : RainbowPath A u v) :
    (⋃ i, (pathsFromEndpoints H hE r u v E A hA p0).A i) = (H : Set G)ᶜ ∪ A := by
  classical
  ext z
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_compl_iff]
  constructor
  · rintro ⟨i, hi⟩
    change z ∈ (if i = 0 then A else {z | (QuotientAddGroup.mk z : G ⧸ H) = i}) at hi
    by_cases hi0 : i = 0
    · exact Or.inr (by simpa only [if_pos hi0] using hi)
    · left
      simp only [if_neg hi0, Set.mem_setOf_eq] at hi
      intro hz
      exact hi0 (hi.symm.trans ((QuotientAddGroup.eq_zero_iff z).mpr hz))
  · rintro (hz | hz)
    · refine ⟨QuotientAddGroup.mk z, ?_⟩
      have hne : (QuotientAddGroup.mk z : G ⧸ H) ≠ 0 :=
        fun h => hz ((QuotientAddGroup.eq_zero_iff z).mp h)
      change z ∈ (if (QuotientAddGroup.mk z : G ⧸ H) = 0 then A else _)
      simp only [if_neg hne, Set.mem_setOf_eq]
    · exact ⟨0, by change z ∈ (if (0 : G ⧸ H) = 0 then A else _); simpa using hz⟩

/-- Actual subgroup gluing, including singleton input. No splitting assumption occurs. -/
theorem cyclic_quotient_glue (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (hq : 3 ≤ Nat.card (G ⧸ H)) (hE : EdgeProperty H)
    (r : G) (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (A : Set G) (hA : A ⊆ (H : Set G)) (c : RainbowCycle A)
    (u v : G) (hu : u ∈ A) (hv : v ∈ A) (hclose : c.next v = u) :
    HasRainbowCycle ((H : Set G)ᶜ ∪ A) := by
  obtain ⟨E⟩ := closed_endpoints_exist hodd H hH hq r u v (hA hu) (hA hv) hgen
  let p0 := RainbowPath.ofFiniteCycle c u v hu hv hclose
  let P := pathsFromEndpoints H hE r u v E A hA p0
  have heq : (⋃ i, P.A i) = (H : Set G)ᶜ ∪ A :=
    pathsFromEndpoints_union H hE r u v E A hA p0
  exact ⟨heq ▸ P.assemble hodd hgen⟩

end SunTwoDeletion
