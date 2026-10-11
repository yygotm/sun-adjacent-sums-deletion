import SunTwoDeletion.Algebra
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.Order.Atoms.Finite

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem proper_subgroup_card_lt (H : AddSubgroup G) (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hx

theorem maximal_quotient_prime (H : AddSubgroup G) (hH : IsCoatom H) :
    (Nat.card (G ⧸ H)).Prime := by
  haveI : IsSimpleAddGroup (G ⧸ H) :=
    AddCommGroup.isSimpleAddGroup_iff_isCoatom.mpr hH
  exact IsSimpleAddGroup.prime_card

theorem exists_prime_quotient [Nontrivial G] :
    ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      (Nat.card (G ⧸ H)).Prime ∧ Nat.card H < Nat.card G := by
  classical
  letI : Finite (AddSubgroup G) :=
    Finite.of_injective (fun H : AddSubgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H, hH⟩ := IsCoatomic.exists_coatom (α := AddSubgroup G)
  exact ⟨H, hH.ne_top, maximal_quotient_prime H hH,
    proper_subgroup_card_lt H hH.ne_top⟩

theorem quotient_generator_lift (H : AddSubgroup G) [IsAddCyclic (G ⧸ H)] :
    ∃ r : G, ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r) := by
  obtain ⟨z, hz⟩ := IsAddCyclic.exists_generator (α := G ⧸ H)
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact ⟨r, hz⟩

theorem quotient_card_nsmul_mem (H : AddSubgroup G) (r : G) :
    (Nat.card (G ⧸ H)) • r ∈ H := by
  rw [← QuotientAddGroup.eq_zero_iff]
  change (QuotientAddGroup.mk' H) ((Nat.card (G ⧸ H)) • r) = 0
  rw [map_nsmul]
  exact card_nsmul_eq_zero'

end SunTwoDeletion
