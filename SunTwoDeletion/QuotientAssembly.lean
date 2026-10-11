import SunTwoDeletion.Assembly
import SunTwoDeletion.Cosets
import SunTwoDeletion.Cyclic

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

noncomputable def doubleEquiv (hodd : Odd (Nat.card G)) : G ≃ G :=
  Equiv.ofBijective (fun x => x + x) ⟨double_injective hodd, double_surjective hodd⟩

theorem doubleEquiv_symm_double (hodd : Odd (Nat.card G)) (x : G) :
    (doubleEquiv hodd).symm (x + x) = x :=
  (doubleEquiv hodd).symm_apply_apply x

theorem double_generator (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) :
    ∀ z : G, z ∈ AddSubgroup.zmultiples (r + r) := by
  intro z
  obtain ⟨w, hw⟩ := double_surjective hodd z
  obtain ⟨n, hn⟩ := hgen w
  change n • r = w at hn
  refine ⟨n, ?_⟩
  change n • (r + r) = z
  rw [smul_add, hn]
  exact hw

/-- The endpoint recurrence is stated in the actual group, so this interface does not
assume that the subgroup is a direct factor. -/
structure CosetPaths (H : AddSubgroup G) (r : G) where
  A : G ⧸ H → Set G
  x : G ⧸ H → G
  y : G ⧸ H → G
  hx : ∀ i, (QuotientAddGroup.mk (x i) : G ⧸ H) = i
  hy : ∀ i, (QuotientAddGroup.mk (y i) : G ⧸ H) = i
  recurrence : ∀ i, x (i + QuotientAddGroup.mk r) = y i + r
  path : ∀ i, RainbowPath (A i) (x i) (y i)
  coset : ∀ i z, z ∈ A i → (QuotientAddGroup.mk z : G ⧸ H) = i

namespace CosetPaths

variable [Finite G] {H : AddSubgroup G} {r : G} (P : CosetPaths H r)

def vertex : (Σ i, Fin (P.path i).len) ↪ G where
  toFun a := (P.path a.1).vertex a.2
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ heq
    have hik : i = k := by
      have hh := congrArg (fun z : G => (QuotientAddGroup.mk z : G ⧸ H)) heq
      rw [P.coset i _ ((P.path i).mem j), P.coset k _ ((P.path k).mem l)] at hh
      exact hh
    subst k
    have hjl := (P.path i).vertex.injective heq
    change j = l at hjl
    subst l
    rfl

theorem vertex_range : Set.range P.vertex = ⋃ i, P.A i := by
  ext z
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, (P.path i).mem j⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := (P.path i).range_vertex.symm.subset hi
    exact ⟨⟨i, j⟩, hj⟩

noncomputable def data (hodd : Odd (Nat.card G))
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r)) :
    BlockData (G ⧸ H) G where
  len i := (P.path i).len
  positive i := (P.path i).positive
  order := Equiv.addRight ((QuotientAddGroup.mk r : G ⧸ H) + QuotientAddGroup.mk r)
  order_cyclic := (generatorCycle (quotient_odd hodd H) _
    (double_generator (quotient_odd hodd H) _ hgen)).cyclic
  reservationOrder := Equiv.addRight (QuotientAddGroup.mk r)
  vertex := P.vertex
  label z := (doubleEquiv (quotient_odd hodd H)).symm (QuotientAddGroup.mk z)
  reserved i := P.x i + P.y i
  reserved_label := by
    intro i
    have hh : (QuotientAddGroup.mk (P.x i + P.y i) : G ⧸ H) = i + i := by
      change (QuotientAddGroup.mk' H) (P.x i + P.y i) = _
      rw [map_add]
      exact congrArg₂ (· + ·) (P.hx i) (P.hy i)
    rw [hh]
    exact doubleEquiv_symm_double _ i
  internal_label := by
    intro i j hj
    have hh : (QuotientAddGroup.mk (P.vertex ⟨i, j⟩ +
        P.vertex ⟨i, ⟨j.val + 1, hj⟩⟩) : G ⧸ H) = i + i := by
      change (QuotientAddGroup.mk' H) ((P.path i).vertex j +
        (P.path i).vertex ⟨j.val + 1, hj⟩) = _
      rw [map_add]
      exact congrArg₂ (· + ·) (P.coset i _ ((P.path i).mem j))
        (P.coset i _ ((P.path i).mem ⟨j.val + 1, hj⟩))
    rw [hh]
    exact doubleEquiv_symm_double _ i
  internal_avoid i j hj := (P.path i).internal_avoid j hj
  internal_injective i j k hj hk := (P.path i).internal_injective j k hj hk
  boundary := by
    intro i j hj
    change (P.path i).vertex j +
      (P.path (i + (QuotientAddGroup.mk r + QuotientAddGroup.mk r))).vertex
        ⟨0, (P.path _).positive⟩ =
      P.x (i + QuotientAddGroup.mk r) + P.y (i + QuotientAddGroup.mk r)
    rw [(P.path i).last j hj, (P.path _).first, ← add_assoc, P.recurrence]
    rw [P.recurrence i]
    abel

noncomputable def assemble (hodd : Odd (Nat.card G))
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r)) :
    RainbowCycle (⋃ i, P.A i) := by
  let c := (P.data hodd hgen).assemble
  exact P.vertex_range ▸ c

theorem internal_edges_preserved (hodd : Odd (Nat.card G))
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (i : G ⧸ H) (j : Fin (P.path i).len) (hj : j.val + 1 < (P.path i).len) :
    (P.data hodd hgen).assemble.next ((P.path i).vertex j) =
      (P.path i).vertex ⟨j.val + 1, hj⟩ := by
  let D := P.data hodd hgen
  change D.assemble.next (D.vertex ⟨i, j⟩) = D.vertex ⟨i, ⟨j.val + 1, hj⟩⟩
  rw [D.assemble_next]
  apply congrArg D.vertex
  change blockNext D.len D.positive D.order ⟨i, j⟩ = _
  have hDj : j.val + 1 < D.len i := hj
  simp only [blockNext, dif_pos hDj]

theorem reserved_colors_present (hodd : Odd (Nat.card G))
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (i : G ⧸ H) :
    P.x i + P.y i ∈ (P.data hodd hgen).assemble.colors :=
  (P.data hodd hgen).reserved_present i

end CosetPaths
end SunTwoDeletion
