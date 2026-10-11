import SunTwoDeletion.Displacements
import Mathlib.Tactic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

theorem exists_nonzero_list [Fintype G] (hcard : 3 ≤ Fintype.card G)
    (n : ℕ) (hn : 2 ≤ n) (t : G) :
    ∃ l : List G, l.length = n ∧ l.sum = t ∧ ∀ x ∈ l, x ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k generalizing t with
  | zero =>
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_nonzero hcard t
    refine ⟨[x,y], rfl, by simpa using hxy, ?_⟩
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> assumption
  | succ k ih =>
    obtain ⟨x, y, hx, _, _⟩ := exists_two_nonzero hcard (0 : G)
    obtain ⟨l, hlen, hsum, hne⟩ := ih (t-x)
    refine ⟨x::l, by simp [hlen]; omega, by simp [hsum], ?_⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact hne z hz

/-- Any fixed pre of displacements can be closed when at least two free
nonzero displacements remain. No direct-factor assumption is involved. -/
theorem displacements_with_prefix [Fintype G] (hcard : 3 ≤ Fintype.card G)
    (pre : List G) (q : ℕ) (hq : pre.length+2 ≤ q) (target : G) :
    ∃ δ : ℕ → G,
      (∀ i, i < pre.length → δ i = pre.getD i 0) ∧
      (∑ i ∈ Finset.range q, δ i) = target ∧
      (∀ i, pre.length ≤ i → i < q → δ i ≠ 0) := by
  obtain ⟨l, hlen, hsum, hne⟩ := exists_nonzero_list hcard (q-pre.length) (by omega)
    (target-pre.sum)
  let L := pre ++ l
  have hL : L.length = q := by simp only [L, List.length_append, hlen]; omega
  refine ⟨fun i => L.getD i 0, ?_, ?_, ?_⟩
  · intro i hi
    simp [L, List.getD, List.getElem?_append, hi]
  · rw [← hL, sum_getD]
    simp [L, hsum]
  · intro i hge hlt
    have hi : ¬ i < pre.length := by omega
    have hil : i-pre.length < l.length := by omega
    have hget : L.getD i 0 = l.getD (i-pre.length) 0 := by
      simp [L, List.getD, List.getElem?_append, hi]
    change L.getD i 0 ≠ 0
    rw [hget]
    exact hne _ (getD_mem_of_lt l _ hil)


theorem displacements_with_prefix_one_or_more [Fintype G]
    (hcard : 3 ≤ Fintype.card G) (pre : List G) (q : ℕ)
    (hq : pre.length+1 ≤ q) (target : G)
    (hres : pre.length+1 = q → target-pre.sum ≠ 0) :
    ∃ δ : ℕ → G,
      (∀ i, i < pre.length → δ i = pre.getD i 0) ∧
      (∑ i ∈ Finset.range q, δ i) = target ∧
      (∀ i, pre.length ≤ i → i < q → δ i ≠ 0) := by
  by_cases htwo : pre.length+2 ≤ q
  · exact displacements_with_prefix hcard pre q htwo target
  have hqeq : pre.length+1=q := by omega
  let L := pre ++ [target-pre.sum]
  have hL : L.length = q := by simp [L]; omega
  refine ⟨fun i => L.getD i 0, ?_, ?_, ?_⟩
  · intro i hi
    simp [L, List.getD, List.getElem?_append, hi]
  · rw [← hL, sum_getD]
    simp [L]
  · intro i hi hlt
    have heq : i = pre.length := by omega
    subst i
    simpa [L, List.getD, List.getElem?_append] using hres hqeq

theorem endpoint_congr_prefix (u r : G) (δ ε : ℕ → G) (i : ℕ)
    (h : ∀ j, j < i → δ j = ε j) :
    endpoint u r δ i = endpoint u r ε i := by
  unfold endpoint
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact h j (Finset.mem_range.mp hj)

end SunThreeDeletion


