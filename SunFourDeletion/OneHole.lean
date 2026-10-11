import SunFourDeletion.PrimeSquare
import SunFourDeletion.Transport
import SunThreeDeletion.OneHoleGroup

set_option autoImplicit false
set_option maxRecDepth 10000
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion
universe u

theorem one_hole_plane :
    HasRainbowCycle ({(0,0)}ᶜ : Set (ZMod 3 × ZMod 3)) :=
  cycle_of_certificate (by decide : 2≤8)
    (![(1,0),(0,1),(1,1),(1,2),(2,0),(0,2),(2,2),(2,1)] : Fin 8 → ZMod 3 × ZMod 3)
    _ (by decide) (by decide) (by decide)

theorem one_hole_zero (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 5≤Nat.card G) :
    HasRainbowCycle ({0}ᶜ : Set G) := by
  suffices aux : ∀ n, ∀ (K : Type u) [AddCommGroup K] [Finite K],
      Nat.card K=n → Odd n → 5≤n → HasRainbowCycle ({0}ᶜ : Set K) from
    aux (Nat.card G) G rfl hodd hsize
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard ho hn
    classical
    have hoddK : Odd (Nat.card K) := hcard.symm ▸ ho
    by_cases hcyc : IsAddCyclic K
    · letI := hcyc
      exact one_hole_cyclic_group K hoddK (by omega)
    haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨H,hproper,hp,hlt⟩ := exists_prime_quotient (G := K)
    haveI : Fact (Nat.card (K ⧸ H)).Prime := ⟨hp⟩
    haveI : IsAddCyclic (K ⧸ H) := isAddCyclic_of_prime_card rfl
    by_cases hH : 5≤Nat.card H
    · have hc := ih (Nat.card H) (by omega) H rfl (subgroup_odd hoddK H) hH
      have hh := lift_finset_cycle hoddK H (by omega) ({0} : Finset H)
        (by simpa using (show 1<Nat.card H by omega)) (by simpa using hc)
      simpa using hh
    have hHsmall : Nat.card H=1 ∨ Nat.card H=3 := by
      obtain ⟨k,hk⟩ := subgroup_odd hoddK H
      have hh : 0<Nat.card H := Nat.card_pos
      omega
    rcases hHsmall with hH1 | hH3
    · have he := H.card_eq_card_quotient_mul_card_addSubgroup
      rw [hH1,mul_one] at he
      haveI : Fact (Nat.card K).Prime := ⟨he.symm ▸ hp⟩
      exact (hcyc (isAddCyclic_of_prime_card rfl)).elim
    haveI : IsAddCyclic H := isAddCyclic_of_prime_card hH3
    by_cases hq : Nat.card (K ⧸ H)=3
    · have h9 : Nat.card K=3^2 := by
        rw [H.card_eq_card_quotient_mul_card_addSubgroup,hH3,hq]
        norm_num
      obtain ⟨e⟩ := prime_square_equiv 3 h9 hcyc
      obtain ⟨C⟩ := one_hole_plane
      have hc := C.map e.toAddMonoidHom e.injective
      have he : e '' ({(0,0)}ᶜ : Set (ZMod 3 × ZMod 3)) = ({0}ᶜ : Set K) := by
        rw [Set.image_compl_eq e.bijective]
        simp only [Set.image_singleton]
        have hz : e (0,0)=0 := e.map_zero
        rw [hz]
      exact ⟨he ▸ hc⟩
    · have hcop : (Nat.card H).Coprime (Nat.card (K ⧸ H)) := by
        rw [hH3]
        exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hq)
      exact (hcyc (cyclic_coprime_extension H hcop)).elim

theorem one_hole (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 5≤Nat.card G) (a : G) :
    HasRainbowCycle ({a}ᶜ : Set G) := by
  obtain ⟨C⟩ := one_hole_zero G hodd hsize
  have h := C.translate a
  have he : (fun x : G => x+a) '' ({0}ᶜ : Set G) = ({a}ᶜ : Set G) := by
    rw [translate_complement]
    simp
  exact ⟨he ▸ h⟩

end SunFourDeletion
