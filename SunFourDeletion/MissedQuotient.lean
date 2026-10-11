import SunFourDeletion.ThreeAvoid
import SunFourDeletion.Transport

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem missed_prime_quotient [Nontrivial G] (hodd : Odd (Nat.card G))
    (hn : ¬ IsAddCyclic G) (D : Finset G) (hD : D.card=4) :
    ∃ H : AddSubgroup G, H≠⊤ ∧ (Nat.card (G ⧸ H)).Prime ∧
      ∃ t : G ⧸ H, ∀ d∈D, QuotientAddGroup.mk d≠t := by
  classical
  by_cases hbig : ∃ H : AddSubgroup G, IsCoatom H ∧ 5≤Nat.card (G ⧸ H)
  · obtain ⟨H,hH,hq⟩ := hbig
    have hsmall : (D.image (QuotientAddGroup.mk' H)).card<Nat.card (G ⧸ H) := by
      have := Finset.card_image_le (s := D) (f := QuotientAddGroup.mk' H)
      omega
    obtain ⟨t,ht⟩ := complement_finset_nonempty (D.image (QuotientAddGroup.mk' H)) hsmall
    refine ⟨H,hH.ne_top,maximal_quotient_prime H hH,t,?_⟩
    intro d hd he
    exact ht (Finset.mem_image.mpr ⟨d,hd,he⟩)
  · have h3 (H : AddSubgroup G) (hH : IsCoatom H) : Nat.card (G ⧸ H)=3 := by
      have hp := (maximal_quotient_prime H hH).two_le
      obtain ⟨k,hk⟩ := quotient_odd hodd H
      have hlt : ¬5≤Nat.card (G ⧸ H) := fun hh => hbig ⟨H,hH,hh⟩
      omega
    obtain ⟨H,L,hH,hL,hne⟩ := two_distinct_maximal hn
    obtain ⟨F,hF⟩ := plane_quotient_of_two_maximal H L hH hL hne (h3 H hH) (h3 L hL)
    obtain ⟨f,hf,t,ht⟩ := three_hom_avoids_four F hF D hD
    let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf
    have hc : Nat.card (G ⧸ f.ker)=3 := by
      have hh := Nat.card_congr e.toEquiv
      simpa using hh
    have hproper : f.ker≠⊤ := by
      intro he
      obtain ⟨x,hx⟩ := hf 1
      have hz : f x=0 := by change x∈f.ker; rw [he]; trivial
      exact one_ne_zero (hx.symm.trans hz)
    refine ⟨f.ker,hproper,hc.symm ▸ (by decide : Nat.Prime 3),e.symm t,?_⟩
    intro d hd he
    apply ht d hd
    have hh := congrArg e he
    rw [e.apply_symm_apply] at hh
    exact hh

end SunFourDeletion
