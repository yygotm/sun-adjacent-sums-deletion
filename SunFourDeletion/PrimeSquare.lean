import SunThreeDeletion.SmallStructure

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

theorem prime_square_equiv {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hcard : Nat.card G=p^2) (hn : ¬ IsAddCyclic G) :
    Nonempty ((ZMod p × ZMod p) ≃+ G) := by
  have hp := (Fact.out : p.Prime).two_le
  have hdvd : p ∣ Nat.card G := by rw [hcard,pow_two]; exact dvd_mul_right p p
  obtain ⟨d,hd⟩ := exists_prime_addOrderOf_dvd_card' (G := G) p hdvd
  let H := AddSubgroup.zmultiples d
  have hH : Nat.card H=p := by rw [Nat.card_zmultiples,hd]
  have hq : Nat.card (G ⧸ H)=p := by
    have he := H.card_eq_card_quotient_mul_card_addSubgroup
    rw [hcard,hH,pow_two] at he
    nlinarith
  have hd0 : d≠0 := by
    intro hz
    rw [hz,addOrderOf_zero] at hd
    omega
  obtain ⟨e,_⟩ := prime_square_coordinates p H hH hq d hd0 rfl hn
  exact ⟨e⟩

end SunFourDeletion
