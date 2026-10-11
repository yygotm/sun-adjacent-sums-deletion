import SunTwoDeletion.QuotientAssembly
import SunTwoDeletion.Orbit

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

namespace Rows

variable (hodd : Odd (Nat.card G)) (H : AddSubgroup G) [Fintype (G ⧸ H)]
  (r : G) (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))

def value (a : Σ _ : H, Fin (Fintype.card (G ⧸ H))) : G := a.1 + a.2.val • r

theorem value_quotient (a : Σ _ : H, Fin (Fintype.card (G ⧸ H))) :
    (QuotientAddGroup.mk (value H r a) : G ⧸ H) =
      orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen a.2 := by
  rw [orbitEquiv_apply]
  change (QuotientAddGroup.mk' H) ((a.1 : G) + a.2.val • r) = _
  rw [map_add, map_nsmul]
  have hh : (QuotientAddGroup.mk' H) a.1 = 0 :=
    (QuotientAddGroup.eq_zero_iff (a.1 : G)).mpr a.1.property
  rw [hh, zero_add]
  rfl

include hodd hgen in
theorem value_injective : Function.Injective (value H r) := by
  rintro ⟨h, j⟩ ⟨k, l⟩ heq
  have hjl : j = l := by
    apply (orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen).injective
    have hh := congrArg (fun z : G => (QuotientAddGroup.mk z : G ⧸ H)) heq
    simpa only [value_quotient hodd H r hgen] using hh
  subst l
  have hhk : h = k := Subtype.ext (add_right_cancel heq)
  subst k
  rfl

def vertex : (Σ _ : H, Fin (Fintype.card (G ⧸ H))) ↪ G :=
  ⟨value H r, value_injective hodd H r hgen⟩

theorem vertex_range : Set.range (vertex hodd H r hgen) = Set.univ := by
  apply Set.range_eq_univ.mpr
  intro z
  let e := orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen
  let j := e.symm (QuotientAddGroup.mk z)
  have hj : (QuotientAddGroup.mk z : G ⧸ H) = j.val • QuotientAddGroup.mk r := by
    exact (e.apply_symm_apply _).symm.trans (orbitEquiv_apply _ _ _ j)
  have hm : z - j.val • r ∈ H := by
    rw [← QuotientAddGroup.eq_zero_iff]
    change (QuotientAddGroup.mk' H) (z - j.val • r) = 0
    rw [map_sub, map_nsmul]
    exact sub_eq_zero.mpr hj
  refine ⟨⟨⟨z - j.val • r, hm⟩, j⟩, ?_⟩
  change (z - j.val • r) + j.val • r = z
  exact sub_add_cancel _ _

variable (c : RainbowCycle (Set.univ : Set H))

noncomputable def next : Equiv.Perm (Σ _ : H, Fin (Fintype.card (G ⧸ H))) :=
  blockPerm (fun _ => Fintype.card (G ⧸ H)) (fun _ => Fintype.card_pos) c.next

noncomputable def color (a : Σ _ : H, Fin (Fintype.card (G ⧸ H))) : G :=
  value H r a + value H r (next H c a)

theorem color_quotient (a : Σ _ : H, Fin (Fintype.card (G ⧸ H))) :
    (QuotientAddGroup.mk (color H r c a) : G ⧸ H) =
      (orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen a.2 +
       orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen a.2) +
      QuotientAddGroup.mk r := by
  obtain ⟨h, j⟩ := a
  change (QuotientAddGroup.mk' H) (value H r ⟨h, j⟩ + value H r (next H c ⟨h, j⟩)) = _
  rw [map_add]
  change (QuotientAddGroup.mk (value H r ⟨h, j⟩) : G ⧸ H) +
    QuotientAddGroup.mk (value H r (next H c ⟨h, j⟩)) = _
  rw [value_quotient hodd H r hgen, value_quotient hodd H r hgen]
  by_cases hj : j.val + 1 < Fintype.card (G ⧸ H)
  · have hnext : next H c ⟨h, j⟩ = ⟨h, ⟨j.val + 1, hj⟩⟩ := by
      simp only [next, blockPerm_apply, blockNext, dif_pos hj]
    rw [hnext, orbitEquiv_succ _ _ _ j hj]
    abel
  · have hnext : next H c ⟨h, j⟩ = ⟨c.next h, ⟨0, Fintype.card_pos⟩⟩ := by
      simp only [next, blockPerm_apply, blockNext, dif_neg hj]
    rw [hnext, orbitEquiv_zero, add_zero]
    have hh := orbitEquiv_last (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen j hj
    rw [add_assoc, hh, add_zero]

include hodd hgen in
theorem color_injective : Function.Injective (color H r c) := by
  rintro ⟨h, j⟩ ⟨k, l⟩ heq
  have hjl : j = l := by
    apply (orbitEquiv (quotient_odd hodd H) (QuotientAddGroup.mk r) hgen).injective
    apply double_injective (quotient_odd hodd H)
    have hh := congrArg (fun z : G => (QuotientAddGroup.mk z : G ⧸ H)) heq
    rw [color_quotient hodd H r hgen c, color_quotient hodd H r hgen c] at hh
    exact add_right_cancel hh
  subst l
  have hhk : h = k := by
    by_cases hj : j.val + 1 < Fintype.card (G ⧸ H)
    · have hnext (a : H) : next H c ⟨a, j⟩ = ⟨a, ⟨j.val + 1, hj⟩⟩ := by
        simp only [next, blockPerm_apply, blockNext, dif_pos hj]
      change value H r ⟨h, j⟩ + value H r (next H c ⟨h, j⟩) =
        value H r ⟨k, j⟩ + value H r (next H c ⟨k, j⟩) at heq
      rw [hnext h, hnext k] at heq
      change ((h : G) + j.val • r) + ((h : G) + (j.val + 1) • r) =
        ((k : G) + j.val • r) + ((k : G) + (j.val + 1) • r) at heq
      apply Subtype.ext
      apply double_injective hodd
      change (h : G) + (h : G) = (k : G) + (k : G)
      apply add_right_cancel (b := j.val • r + (j.val + 1) • r)
      calc
        _ = ((h : G) + j.val • r) + ((h : G) + (j.val + 1) • r) := by ac_rfl
        _ = ((k : G) + j.val • r) + ((k : G) + (j.val + 1) • r) := heq
        _ = _ := by ac_rfl
    · have hnext (a : H) : next H c ⟨a, j⟩ = ⟨c.next a, ⟨0, Fintype.card_pos⟩⟩ := by
        simp only [next, blockPerm_apply, blockNext, dif_neg hj]
      change value H r ⟨h, j⟩ + value H r (next H c ⟨h, j⟩) =
        value H r ⟨k, j⟩ + value H r (next H c ⟨k, j⟩) at heq
      rw [hnext h, hnext k] at heq
      change ((h : G) + j.val • r) + ((c.next h : G) + 0 • r) =
        ((k : G) + j.val • r) + ((c.next k : G) + 0 • r) at heq
      simp only [zero_nsmul, add_zero] at heq
      apply c.rainbow trivial trivial
      apply Subtype.ext
      change (h : G) + (c.next h : G) = (k : G) + (c.next k : G)
      apply add_right_cancel (b := j.val • r)
      calc
        _ = ((h : G) + j.val • r) + (c.next h : G) := by abel
        _ = ((k : G) + j.val • r) + (c.next k : G) := heq
        _ = _ := by abel
  subst k
  rfl

noncomputable def cycle : RainbowCycle (Set.range (vertex hodd H r hgen)) :=
  RainbowCycle.ofEmbedding (next H c)
    (blockPerm_cyclic _ _ c.next c.cyclic) (vertex hodd H r hgen)
    (color_injective hodd H r hgen c)

theorem cycle_edge (hq : 1 < Fintype.card (G ⧸ H)) :
    (cycle hodd H r hgen c).next 0 = r := by
  let j : Fin (Fintype.card (G ⧸ H)) := ⟨0, by omega⟩
  have h0 : vertex hodd H r hgen ⟨0, j⟩ = 0 := by
    change (0 : G) + 0 • r = 0
    simp
  have hn : (cycle hodd H r hgen c).next (vertex hodd H r hgen ⟨0, j⟩) =
      vertex hodd H r hgen (next H c ⟨0, j⟩) :=
    RainbowCycle.ofEmbedding_next _ _ _ _ _
  rw [← h0, hn]
  change value H r (next H c ⟨0, j⟩) = r
  have hj : j.val + 1 < Fintype.card (G ⧸ H) := hq
  simp only [next, blockPerm_apply, blockNext, dif_pos hj]
  change (0 : G) + 1 • r = r
  simp

include hodd hgen c in
theorem exists_full_cycle_with_edge (hq : 1 < Fintype.card (G ⧸ H)) :
    ∃ C : RainbowCycle (Set.univ : Set G), C.next 0 = r := by
  let C := cycle hodd H r hgen c
  have heq := vertex_range hodd H r hgen
  let D : RainbowCycle (Set.univ : Set G) :=
    ⟨C.next, by rw [← heq]; exact C.cyclic, by rw [← heq]; exact C.rainbow⟩
  exact ⟨D, cycle_edge hodd H r hgen c hq⟩

end Rows
end SunTwoDeletion
