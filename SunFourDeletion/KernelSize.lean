import SunFourDeletion.MaximalQuotients

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

theorem large_prime_kernel {G : Type*} [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hn : ¬ IsAddCyclic G)
    (h9 : Nat.card G≠9) (h25 : Nat.card G≠25)
    (H : AddSubgroup G) (hp : (Nat.card (G ⧸ H)).Prime) : 7≤Nat.card H := by
  haveI : Fact (Nat.card (G ⧸ H)).Prime := ⟨hp⟩
  haveI : IsAddCyclic (G ⧸ H) := isAddCyclic_of_prime_card rfl
  by_contra hlarge
  have hsmall : Nat.card H=1 ∨ Nat.card H=3 ∨ Nat.card H=5 := by
    obtain ⟨k,hk⟩ := subgroup_odd hodd H
    have hh : 0<Nat.card H := Nat.card_pos
    omega
  rcases hsmall with h1 | h3 | h5
  · have he := H.card_eq_card_quotient_mul_card_addSubgroup
    rw [h1,mul_one] at he
    haveI : Fact (Nat.card G).Prime := ⟨he.symm ▸ hp⟩
    exact hn (isAddCyclic_of_prime_card rfl)
  · haveI : IsAddCyclic H := isAddCyclic_of_prime_card h3
    have hq : Nat.card (G ⧸ H)≠3 := by
      intro he
      apply h9
      rw [H.card_eq_card_quotient_mul_card_addSubgroup,h3,he]
    apply hn (cyclic_coprime_extension H ?_)
    rw [h3]
    exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hq)
  · haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    haveI : IsAddCyclic H := isAddCyclic_of_prime_card h5
    have hq : Nat.card (G ⧸ H)≠5 := by
      intro he
      apply h25
      rw [H.card_eq_card_quotient_mul_card_addSubgroup,h5,he]
    apply hn (cyclic_coprime_extension H ?_)
    rw [h5]
    exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hq)

end SunFourDeletion
