import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

theorem double_injective (hodd : Odd (Nat.card G)) :
    Function.Injective (fun x : G => x + x) := by
  simpa only [two_nsmul] using
    (hodd.coprime_two_right.nsmul_right_bijective (G := G)).1

theorem double_surjective (hodd : Odd (Nat.card G)) :
    Function.Surjective (fun x : G => x + x) := by
  simpa only [two_nsmul] using
    (hodd.coprime_two_right.nsmul_right_bijective (G := G)).2

theorem missing_colors_ne (hodd : Odd (Nat.card G)) {a b : G} (hab : a ≠ b) :
    3 • a - b ≠ 3 • b - a := by
  intro h
  have h4 : (a + a) + (a + a) = (b + b) + (b + b) := by
    calc
      (a + a) + (a + a) = (3 • a - b) + (a + b) := by abel
      _ = (3 • b - a) + (a + b) := congrArg (· + (a + b)) h
      _ = (b + b) + (b + b) := by abel
  exact hab (double_injective hodd (double_injective hodd h4))

theorem missing_colors_sum (a b : G) :
    (3 • a - b) + (3 • b - a) = (a + b) + (a + b) := by
  abel

theorem translated_missing_left (a d : G) :
    a + a + (-d) = 3 • a - (a + d) := by
  abel

theorem translated_missing_right (a d : G) :
    a + a + 3 • d = 3 • (a + d) - a := by
  abel

theorem subgroup_odd (hodd : Odd (Nat.card G)) (H : AddSubgroup G) :
    Odd (Nat.card H) :=
  hodd.of_dvd_nat H.card_addSubgroup_dvd_card

theorem quotient_odd (hodd : Odd (Nat.card G)) (H : AddSubgroup G) :
    Odd (Nat.card (G ⧸ H)) :=
  hodd.of_dvd_nat H.card_quotient_dvd_card

theorem exists_two_nonzero [Fintype G] (hcard : 3 ≤ Fintype.card G) (t : G) :
    ∃ c d : G, c ≠ 0 ∧ d ≠ 0 ∧ c + d = t := by
  classical
  have hex : ∃ c : G, c ≠ 0 ∧ c ≠ t := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset G) ⊆ {0, t} := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have hc := Finset.card_le_card hsub
    have hp : ({0, t} : Finset G).card ≤ 2 := by
      by_cases ht : t = 0 <;> simp [ht, eq_comm]
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨c, hc, hct⟩ := hex
  refine ⟨c, t - c, hc, ?_, ?_⟩
  · exact fun h => hct (sub_eq_zero.mp h).symm
  · abel

theorem exists_even_nonzero_list [Fintype G] (hcard : 3 ≤ Fintype.card G)
    (s : ℕ) (t : G) :
    ∃ l : List G, l.length = 2 * (s + 1) ∧ l.sum = t ∧ ∀ x ∈ l, x ≠ 0 := by
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_two_nonzero hcard t
  induction s with
  | zero =>
    refine ⟨[c, d], by simp, by simpa using hcd, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hd
  | succ s ih =>
    obtain ⟨l, hlen, hsum, hne⟩ := ih
    refine ⟨c :: -c :: l, ?_, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
      omega
    · simp [hsum]
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hc
      · exact neg_ne_zero.mpr hc
      · exact hne x hx

theorem joining_color (r xi yi xj yj : G)
    (hleft : xi = yi + r) (hright : xj = yj + r) :
    yi + xj = xi + yj := by
  rw [hleft, hright]
  abel

def endpoint (u r : G) (δ : ℕ → G) (i : ℕ) : G :=
  u + i • r + ∑ j ∈ Finset.range i, δ j

theorem endpoint_zero (u r : G) (δ : ℕ → G) :
    endpoint u r δ 0 = u := by
  simp [endpoint]

theorem endpoint_succ (u r : G) (δ : ℕ → G) (i : ℕ) :
    endpoint u r δ (i + 1) = endpoint u r δ i + δ i + r := by
  simp only [endpoint, add_nsmul, one_nsmul, Finset.sum_range_succ]
  abel

theorem endpoint_closes (u r : G) (δ : ℕ → G) (q : ℕ)
    (h : ∑ j ∈ Finset.range q, δ j = -(q • r)) :
    endpoint u r δ q = u := by
  simp [endpoint, h]

end SunTwoDeletion
