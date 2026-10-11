import SunTwoDeletion.Glue

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem CosetPaths.zero_color_control {H : AddSubgroup G} {r : G}
    (P : CosetPaths H r) (hodd : Odd (Nat.card G))
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (C : Set G) (hreserved : P.x 0 + P.y 0 ∈ C)
    (hinternal : ∀ (j : Fin (P.path 0).len) (hj : j.val + 1 < (P.path 0).len),
      (P.path 0).vertex j + (P.path 0).vertex ⟨j.val + 1, hj⟩ ∈ C)
    (z : G) (hz : z ∈ (P.data hodd hgen).assemble.colors) (hzH : z ∈ H) :
    z ∈ C := by
  let D := P.data hodd hgen
  have hlabel : D.label z = 0 := by
    change (doubleEquiv (quotient_odd hodd H)).symm (QuotientAddGroup.mk z) = 0
    rw [(QuotientAddGroup.eq_zero_iff z).mpr hzH]
    simpa only [zero_add] using doubleEquiv_symm_double (quotient_odd hodd H) 0
  rw [D.assemble_colors] at hz
  obtain ⟨⟨i, j⟩, rfl⟩ := hz
  by_cases hj : j.val + 1 < D.len i
  · have hi : i = 0 := by
      rw [D.color_internal i j hj, D.internal_label] at hlabel
      exact hlabel
    subst i
    rw [D.color_internal 0 j hj]
    exact hinternal j hj
  · have hi : D.reservationOrder i = 0 := by
      rw [D.color_boundary i j hj, D.reserved_label] at hlabel
      exact hlabel
    rw [D.color_boundary i j hj, hi]
    exact hreserved

/-- The full gluing statement used by induction: preserve every uncut input edge,
and introduce no new color lying in the subgroup. -/
theorem cyclic_quotient_glue_controlled (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (hq : 3 ≤ Nat.card (G ⧸ H)) (hE : EdgeProperty H)
    (r : G) (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (A : Set G) (hA : A ⊆ (H : Set G)) (c : RainbowCycle A)
    (u v : G) (hu : u ∈ A) (hv : v ∈ A) (hclose : c.next v = u) :
    ∃ C : RainbowCycle ((H : Set G)ᶜ ∪ A),
      (∀ z ∈ A, z ≠ v → C.next z = c.next z) ∧
      (∀ z ∈ C.colors, z ∈ H → z ∈ c.colors) := by
  classical
  obtain ⟨E⟩ := closed_endpoints_exist hodd H hH hq r u v (hA hu) (hA hv) hgen
  let p0 := RainbowPath.ofFiniteCycle c u v hu hv hclose
  let P := pathsFromEndpoints H hE r u v E A hA p0
  let D := P.data hodd hgen
  have hA0 : P.A 0 = A := by simp [P, pathsFromEndpoints]
  let pzero : RainbowPath (P.A 0) (P.x 0) (P.y 0) :=
    ⟨p0.len, p0.positive, p0.vertex, p0.range_vertex.trans hA0.symm,
      p0.first.trans E.x_zero.symm,
      fun j hj => (p0.last j hj).trans E.y_zero.symm,
      p0.internal_injective, by
        intro j hj
        change p0.vertex j + p0.vertex ⟨j.val + 1, hj⟩ ≠ E.x 0 + E.y 0
        rw [E.x_zero, E.y_zero]
        exact p0.internal_avoid j hj⟩
  have hpath : P.path 0 = pzero := by
    simp [P, pathsFromEndpoints, pzero]
  have hsource : ∀ (j : Fin (P.path 0).len) (hj : j.val + 1 < (P.path 0).len),
      c.next ((P.path 0).vertex j) = (P.path 0).vertex ⟨j.val + 1, hj⟩ := by
    rw [hpath]
    exact RainbowPath.ofFiniteCycle_internal_next c u v hu hv hclose
  have heq : Set.range D.vertex = (H : Set G)ᶜ ∪ A :=
    P.vertex_range.trans (pathsFromEndpoints_union H hE r u v E A hA p0)
  let C : RainbowCycle ((H : Set G)ᶜ ∪ A) :=
    ⟨D.assemble.next, by rw [← heq]; exact D.assemble.cyclic,
      by rw [← heq]; exact D.assemble.rainbow⟩
  have hcolors : C.colors = D.assemble.colors :=
    congrArg (fun S : Set G => (fun z => z + D.assemble.next z) '' S) heq.symm
  refine ⟨C, ?_, ?_⟩
  · intro z hz hzv
    have hz0 : z ∈ P.A 0 := hA0.symm.subset hz
    obtain ⟨j, hjz⟩ := (P.path 0).range_vertex.symm.subset hz0
    have hj : j.val + 1 < (P.path 0).len := by
      by_contra hj
      have hh := (P.path 0).last j hj
      have hy0 : P.y 0 = v := E.y_zero
      exact hzv (hjz.symm.trans (hh.trans hy0))
    change D.assemble.next z = c.next z
    rw [← hjz, P.internal_edges_preserved hodd hgen 0 j hj, hsource j hj]
  · intro z hz hzH
    rw [hcolors] at hz
    apply P.zero_color_control hodd hgen c.colors ?_ ?_ z hz hzH
    · have hx0 : P.x 0 = u := E.x_zero
      have hy0 : P.y 0 = v := E.y_zero
      rw [hx0, hy0]
      exact ⟨v, hv, by change v + c.next v = u + v; rw [hclose]; abel⟩
    · intro j hj
      refine ⟨(P.path 0).vertex j, hA0.subset ((P.path 0).mem j), ?_⟩
      change (P.path 0).vertex j + c.next ((P.path 0).vertex j) = _
      rw [hsource j hj]

end SunTwoDeletion
