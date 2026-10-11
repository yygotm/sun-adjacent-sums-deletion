import SunTwoDeletion.Paths
import SunTwoDeletion.Subgroups

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

def cosetEmbedding (H : AddSubgroup G) (x : G) : H ↪ G where
  toFun h := x + h
  inj' := by
    intro h k heq
    exact Subtype.ext (add_left_cancel heq)

theorem cosetEmbedding_range (H : AddSubgroup G) (x : G) :
    Set.range (cosetEmbedding H x) = {z | QuotientAddGroup.mk z = (QuotientAddGroup.mk x : G ⧸ H)} := by
  ext z
  constructor
  · rintro ⟨h, rfl⟩
    change (QuotientAddGroup.mk' H) (x + h) = _
    rw [map_add]
    have hh : (QuotientAddGroup.mk' H) h = 0 := by
      change (QuotientAddGroup.mk (h : G) : G ⧸ H) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact h.property
    rw [hh, add_zero]
    rfl
  · intro hz
    have hm : z - x ∈ H := by
      rw [← QuotientAddGroup.eq_zero_iff]
      change (QuotientAddGroup.mk' H) (z - x) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hz
    refine ⟨⟨z - x, hm⟩, ?_⟩
    change x + (z - x) = z
    abel

noncomputable def fullCosetCycle (H : AddSubgroup G) (x : G)
    (c : RainbowCycle (Set.univ : Set H)) : RainbowCycle (Set.range (cosetEmbedding H x)) :=
  RainbowCycle.ofEmbedding c.next c.cyclic (cosetEmbedding H x) (by
    intro h k heq
    apply c.rainbow (Set.mem_univ _) (Set.mem_univ _)
    apply Subtype.ext
    change (h : G) + (c.next h : G) = (k : G) + (c.next k : G)
    change (x + (h : G)) + (x + (c.next h : G)) =
      (x + (k : G)) + (x + (c.next k : G)) at heq
    have heq' : (x + x) + ((h : G) + (c.next h : G)) =
        (x + x) + ((k : G) + (c.next k : G)) := by
      calc
        _ = (x + (h : G)) + (x + (c.next h : G)) := by abel
        _ = (x + (k : G)) + (x + (c.next k : G)) := heq
        _ = _ := by abel
    exact add_left_cancel heq')

theorem fullCosetCycle_next (H : AddSubgroup G) (x : G)
    (c : RainbowCycle (Set.univ : Set H)) (h : H) :
    (fullCosetCycle H x c).next (x + h) = x + c.next h :=
  RainbowCycle.ofEmbedding_next _ _ _ _ h

theorem fullCosetCycle_colors [Finite G] (H : AddSubgroup G) (x : G)
    (c : RainbowCycle (Set.univ : Set H)) :
    (fullCosetCycle H x c).colors =
      {z | QuotientAddGroup.mk z = (QuotientAddGroup.mk (x + x) : G ⧸ H)} := by
  have he : (fullCosetCycle H x c).colors =
      Set.range (fun h : H => cosetEmbedding H x h + cosetEmbedding H x (c.next h)) :=
    RainbowCycle.ofEmbedding_colors _ _ _ _
  rw [he, ← cosetEmbedding_range]
  have hc : Function.Surjective (fun h : H => h + c.next h) :=
    Finite.surjective_of_injective (fun _ _ h => c.rainbow trivial trivial h)
  ext z
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h + c.next h, ?_⟩
    change (x + x) + ((h : G) + (c.next h : G)) =
      (x + (h : G)) + (x + (c.next h : G))
    abel
  · rintro ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := hc h
    refine ⟨k, ?_⟩
    have hkg := congrArg (fun a : H => (a : G)) hk
    change (k : G) + (c.next k : G) = (h : G) at hkg
    change (x + (k : G)) + (x + (c.next k : G)) = (x + x) + (h : G)
    calc
      _ = (x + x) + ((k : G) + (c.next k : G)) := by abel
      _ = _ := by rw [hkg]

theorem coset_path_exists [Finite G] (H : AddSubgroup G) (hE : EdgeProperty H)
    (x y : G) (hxy : x ≠ y)
    (hcoset : (QuotientAddGroup.mk x : G ⧸ H) = QuotientAddGroup.mk y) :
    Nonempty (RainbowPath {z | QuotientAddGroup.mk z = (QuotientAddGroup.mk x : G ⧸ H)} x y) := by
  have hm : y - x ∈ H := by
    rw [← QuotientAddGroup.eq_zero_iff]
    change (QuotientAddGroup.mk' H) (y - x) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hcoset.symm
  let d : H := ⟨y - x, hm⟩
  have hd : d ≠ 0 := by
    intro h
    have hh := congrArg (fun a : H => (a : G)) h
    change y - x = 0 at hh
    exact hxy (sub_eq_zero.mp hh).symm
  obtain ⟨c, hc⟩ := hE d 0 hd
  let c' := fullCosetCycle H x c
  have hx : x ∈ Set.range (cosetEmbedding H x) := by
    refine ⟨0, ?_⟩
    change x + (0 : G) = x
    exact add_zero x
  have hy : y ∈ Set.range (cosetEmbedding H x) := by
    refine ⟨d, ?_⟩
    change x + (y - x) = y
    abel
  have hclose : c'.next y = x := by
    have heq : y = x + (d : G) := by dsimp [d]; abel
    rw [heq, fullCosetCycle_next, hc]
    simp
  have p := RainbowPath.ofFiniteCycle c' x y hx hy hclose
  exact ⟨cosetEmbedding_range H x ▸ p⟩

end SunTwoDeletion
