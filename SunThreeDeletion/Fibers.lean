import SunThreeDeletion.IndexedEndpoints

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

def deletedFiber (H : AddSubgroup G)
    (e : Fin (Nat.card (G ⧸ H)) ≃ (G ⧸ H)) (D : Set G)
    (j : Fin (Nat.card (G ⧸ H))) : Set G :=
  {z | (QuotientAddGroup.mk z : G ⧸ H) = e j} \ D

theorem deletedFiber_union (H : AddSubgroup G)
    (e : Fin (Nat.card (G ⧸ H)) ≃ (G ⧸ H)) (D : Set G) :
    (⋃ j, deletedFiber H e D j) = Dᶜ := by
  ext z
  simp only [Set.mem_iUnion, deletedFiber, Set.mem_diff, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨j,hj,hz⟩
    exact hz
  · intro hz
    exact ⟨e.symm (QuotientAddGroup.mk z), by simp, hz⟩

theorem deletedFiber_full (H : AddSubgroup G)
    (e : Fin (Nat.card (G ⧸ H)) ≃ (G ⧸ H)) (D : Set G) (l : ℕ)
    (hD : ∀ z ∈ D, ∃ i : Fin (Nat.card (G ⧸ H)), i.val<l ∧
      (QuotientAddGroup.mk z : G ⧸ H) = e i)
    (j : Fin (Nat.card (G ⧸ H))) (hj : l ≤ j.val) :
    deletedFiber H e D j = {z | (QuotientAddGroup.mk z : G ⧸ H) = e j} := by
  ext z
  constructor
  · exact fun h => h.1
  · intro hz
    refine ⟨hz, ?_⟩
    intro hd
    obtain ⟨i,hi,he⟩ := hD z hd
    have heq := e.injective (he.symm.trans hz)
    have hv := congrArg Fin.val heq
    omega

theorem fiber_as_image (H : AddSubgroup G) (r : G) (D : Set G) :
    {z | (QuotientAddGroup.mk z : G ⧸ H) = QuotientAddGroup.mk r} \ D =
      (fun x : H => (x : G)+r) '' {x : H | (x : G)+r ∉ D} := by
  ext z
  constructor
  · rintro ⟨hz,hd⟩
    have hm : z-r ∈ H := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' H) (z-r) = 0
      rw [map_sub]
      change (QuotientAddGroup.mk z : G ⧸ H) - QuotientAddGroup.mk r = 0
      rw [hz, sub_self]
    exact ⟨⟨z-r,hm⟩, by simpa using hd, sub_add_cancel z r⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_, hx⟩
    change (QuotientAddGroup.mk' H) ((x : G)+r) = _
    rw [map_add]
    have hx0 : (QuotientAddGroup.mk' H) (x : G) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr x.property
    rw [hx0, zero_add]
    rfl


/-- If one hole lies in each of the first l cosets, its fiber is the translated
one-hole set in H. The assertion follows from quotient injectivity, not a split. -/
theorem fiber_one_hole (H : AddSubgroup G)
    (e : Fin (Nat.card (G ⧸ H)) ≃ (G ⧸ H)) (l : ℕ) (hl : l ≤ Nat.card (G ⧸ H))
    (s : Fin l → G)
    (hs : ∀ i, (QuotientAddGroup.mk (s i) : G ⧸ H) = e ⟨i.val,lt_of_lt_of_le i.isLt hl⟩)
    (j : Fin l) :
    deletedFiber H e (Set.range s) ⟨j.val,lt_of_lt_of_le j.isLt hl⟩ =
      (fun x : H => (x : G)+s j) '' ({0}ᶜ : Set H) := by
  change {z | (QuotientAddGroup.mk z : G ⧸ H) = e _} \ Set.range s = _
  rw [← hs j, fiber_as_image]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · intro h hx
    subst x
    apply h
    exact ⟨j, by simp⟩
  · intro hx ⟨i,hi⟩
    have hq := congrArg (QuotientAddGroup.mk' H) hi
    have hx0 : (QuotientAddGroup.mk' H) (x : G) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr x.property
    rw [map_add,hx0,zero_add] at hq
    change (QuotientAddGroup.mk (s i) : G ⧸ H) =
      QuotientAddGroup.mk (s j) at hq
    rw [hs i, hs j] at hq
    have he := congrArg Fin.val (e.injective hq)
    have hij : i=j := Fin.ext he
    subst i
    apply hx
    apply Subtype.ext
    change (x : G)=0
    exact (add_eq_right.mp hi.symm)

end SunThreeDeletion

