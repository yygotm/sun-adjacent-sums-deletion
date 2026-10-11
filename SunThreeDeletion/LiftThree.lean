import SunThreeDeletion.SubgroupExtension
import Mathlib.Tactic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem complement_three_nonempty (a b c : G) (hcard : 4 ≤ Nat.card G) :
    ({a,b,c}ᶜ : Set G).Nonempty := by
  classical
  letI := Fintype.ofFinite G
  by_contra h
  have hall : ∀ x : G, x ∈ ({a,b,c} : Finset G) := by
    intro x
    by_contra hx
    apply h
    exact ⟨x, by simpa using hx⟩
  have hs : (Finset.univ : Finset G) ⊆ {a,b,c} := fun x _ => hall x
  have hc := Finset.card_le_card hs
  have hb : ({a,b,c} : Finset G).card ≤ 3 := by
    calc
      _ ≤ ({b,c} : Finset G).card+1 := Finset.card_insert_le _ _
      _ ≤ 3 := by
        have hc2 : ({b,c} : Finset G).card ≤ 2 := by
          simpa using Finset.card_insert_le b ({c} : Finset G)
        omega
  simp only [Finset.card_univ] at hc
  rw [Nat.card_eq_fintype_card] at hcard
  omega

theorem lift_three_cycle (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hcard : 4 ≤ Nat.card H) (a b c : H)
    (h : HasRainbowCycle ({a,b,c}ᶜ : Set H)) :
    HasRainbowCycle ({(a:G),(b:G),(c:G)}ᶜ : Set G) := by
  obtain ⟨C⟩ := h
  let A := H.subtype '' ({a,b,c}ᶜ : Set H)
  have hA : A ⊆ H := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have hne : A.Nonempty := (complement_three_nonempty a b c hcard).image H.subtype
  have hh := subgroup_extension G hodd H (by omega) A hA hne
    ⟨C.map H.subtype Subtype.val_injective⟩
  have heq : (H : Set G)ᶜ ∪ A = ({(a:G),(b:G),(c:G)}ᶜ : Set G) := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, A, Set.mem_image,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hz | ⟨x,hx,rfl⟩)
      · rintro (rfl | rfl | rfl)
        · exact hz a.property
        · exact hz b.property
        · exact hz c.property
      · rintro (h | h | h)
        · exact hx (Or.inl (Subtype.ext h))
        · exact hx (Or.inr (Or.inl (Subtype.ext h)))
        · exact hx (Or.inr (Or.inr (Subtype.ext h)))
    · intro hz
      by_cases hH : z ∈ H
      · right
        refine ⟨⟨z,hH⟩, ?_, rfl⟩
        rintro (h | h | h)
        · exact hz (Or.inl (congrArg Subtype.val h))
        · exact hz (Or.inr (Or.inl (congrArg Subtype.val h)))
        · exact hz (Or.inr (Or.inr (congrArg Subtype.val h)))
      · exact Or.inl hH
  rwa [heq] at hh

end SunThreeDeletion

