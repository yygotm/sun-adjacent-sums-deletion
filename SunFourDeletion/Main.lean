import SunFourDeletion.CyclicFour
import SunFourDeletion.SmallGroups
import SunFourDeletion.KernelSize
import SunFourDeletion.MissedQuotient
import SunFourDeletion.InductionStep
import SunFourDeletion.Statement

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion
universe u

/-- Unconditional four-deletion existence, proved by strong induction on group order. -/
theorem four_deletion_cycle (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 7≤Nat.card G) (D : Finset G) (hD : D.card=4) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  suffices aux : ∀ n, ∀ (K : Type u) [AddCommGroup K] [Finite K],
      Nat.card K=n → Odd n → 7≤n →
      ∀ E : Finset K, E.card=4 → HasRainbowCycle ((E : Set K)ᶜ) from
    aux (Nat.card G) G rfl hodd hsize D hD
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard ho hn E hE
    classical
    have hoddK : Odd (Nat.card K) := hcard.symm ▸ ho
    by_cases hcyc : IsAddCyclic K
    · letI := hcyc
      exact cyclic_four_cycle K hoddK (by omega) E hE
    by_cases h9 : Nat.card K=9
    · exact noncyclic_nine_four h9 hcyc E hE
    by_cases h25 : Nat.card K=25
    · exact noncyclic_twentyfive_four h25 hcyc E hE
    haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨H,hproper,hp,v,hv⟩ := missed_prime_quotient hoddK hcyc E hE
    have hH := large_prime_kernel hoddK hcyc h9 h25 H hp
    haveI : Fact (Nat.card (K ⧸ H)).Prime := ⟨hp⟩
    haveI : IsAddCyclic (K ⧸ H) := isAddCyclic_of_prime_card rfl
    have hq : 3≤Nat.card (K ⧸ H) := by
      have h2 := hp.two_le
      obtain ⟨k,hk⟩ := quotient_odd hoddK H
      omega
    apply four_via_large_subgroup hoddK H hH hq E hE v hv
    intro F hF
    have hlt := proper_subgroup_card_lt H hproper
    exact ih (Nat.card H) (by omega) H rfl (subgroup_odd hoddK H) hH F hF

variable {G : Type u} [AddCommGroup G] [Finite G]

theorem sun_four_deletion_finset (hodd : Odd (Nat.card G)) (hsize : 7≤Nat.card G)
    (D : Finset G) (hD : D.card=4) :
    ∃ (n : ℕ) (hn : 0<n) (v : Fin n ↪ G),
      n=Nat.card G-4 ∧ 2<n ∧ Set.range v=(D : Set G)ᶜ ∧
      Function.Injective (fun i => v i+v (cyclicSuccessor hn i)) :=
  ordering_of_four_cycle hsize D hD (four_deletion_cycle G hodd hsize D hD)

/-- Four distinct removed elements; the indexed conclusion matches the three-deletion API. -/
theorem sun_four_deletion (hodd : Odd (Nat.card G)) (hsize : 7≤Nat.card G)
    (a b c d : G) (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    ∃ (n : ℕ) (hn : 0<n) (v : Fin n ↪ G),
      n=Nat.card G-4 ∧ 2<n ∧ Set.range v=({a,b,c,d}ᶜ : Set G) ∧
      Function.Injective (fun i => v i+v (cyclicSuccessor hn i)) := by
  classical
  have hh := sun_four_deletion_finset hodd hsize ({a,b,c,d} : Finset G)
    (four_finset_card a b c d hab hac had hbc hbd hcd)
  simpa using hh

end SunFourDeletion
