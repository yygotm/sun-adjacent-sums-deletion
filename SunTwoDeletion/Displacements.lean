import SunTwoDeletion.Subgroups

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

theorem sum_getD (l : List G) :
    ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simpa only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons, add_comm a] using
      congrArg (· + a) ih

theorem getD_mem_of_lt (l : List G) (i : ℕ) (hi : i < l.length) :
    l.getD i 0 ∈ l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hil : i < l.length := by simpa using hi
      simpa only [List.getD_cons_succ] using List.mem_cons_of_mem a (ih i hil)

/-- Any prescribed first displacement can be completed to a closed odd-length chain,
with all subsequent displacements nonzero. The target t will be -(q • r). -/
theorem exists_displacements [Fintype G] (hcard : 3 ≤ Fintype.card G)
    (q : ℕ) (hqodd : Odd q) (hq : 3 ≤ q) (first target : G) :
    ∃ δ : ℕ → G, δ 0 = first ∧
      (∑ i ∈ Finset.range q, δ i) = target ∧
      ∀ i, 0 < i → i < q → δ i ≠ 0 := by
  obtain ⟨k, hk⟩ := hqodd
  have hkpos : 0 < k := by omega
  obtain ⟨l, hlen, hsum, hnonzero⟩ :=
    exists_even_nonzero_list hcard (k - 1) (target - first)
  have hlen' : l.length + 1 = q := by omega
  let L := first :: l
  refine ⟨fun i => L.getD i 0, ?_, ?_, ?_⟩
  · simp [L]
  · have hL : L.length = q := by simpa [L] using hlen'
    rw [← hL, sum_getD]
    simp [L, hsum]
  · intro i hi hiq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    change (first :: l).getD (j + 1) 0 ≠ 0
    rw [List.getD_cons_succ]
    exact hnonzero _ (getD_mem_of_lt l j (by omega))

theorem endpoint_quotient (H : AddSubgroup G) (u r : G) (hu : u ∈ H)
    (δ : ℕ → G) (hδ : ∀ i, δ i ∈ H) (i : ℕ) :
    (QuotientAddGroup.mk (endpoint u r δ i) : G ⧸ H) =
      i • (QuotientAddGroup.mk r : G ⧸ H) := by
  induction i with
  | zero =>
    rw [endpoint_zero, zero_nsmul]
    exact (QuotientAddGroup.eq_zero_iff u).mpr hu
  | succ i ih =>
    rw [endpoint_succ]
    change (QuotientAddGroup.mk' H) (endpoint u r δ i + δ i + r) = _
    rw [map_add, map_add]
    have hz : (QuotientAddGroup.mk' H) (δ i) = 0 :=
      (QuotientAddGroup.eq_zero_iff (δ i)).mpr (hδ i)
    rw [hz, add_zero]
    change (QuotientAddGroup.mk (endpoint u r δ i) : G ⧸ H) + QuotientAddGroup.mk r = _
    rw [ih, succ_nsmul]

theorem exists_closed_displacements [Finite G] (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (r u v : G) (hu : u ∈ H) (hv : v ∈ H)
    (hqodd : Odd (Nat.card (G ⧸ H))) (hq : 3 ≤ Nat.card (G ⧸ H)) :
    ∃ δ : ℕ → G, δ 0 = v - u ∧
      (∀ i, δ i ∈ H) ∧
      (∀ i, 0 < i → i < Nat.card (G ⧸ H) → δ i ≠ 0) ∧
      endpoint u r δ (Nat.card (G ⧸ H)) = u := by
  classical
  letI := Fintype.ofFinite H
  let q := Nat.card (G ⧸ H)
  have ht : -(q • r) ∈ H := H.neg_mem (quotient_card_nsmul_mem H r)
  obtain ⟨δ, hfirst, hsum, hne⟩ := exists_displacements
    (by simpa only [Nat.card_eq_fintype_card] using hH) q hqodd hq
    (⟨v - u, H.sub_mem hv hu⟩ : H) (⟨-(q • r), ht⟩ : H)
  refine ⟨fun i => (δ i : G), ?_, fun i => (δ i).property, ?_, ?_⟩
  · exact congrArg (fun a : H => (a : G)) hfirst
  · intro i hi hiq heq
    exact hne i hi hiq (Subtype.ext heq)
  · apply endpoint_closes
    have hh := congrArg (fun a : H => (a : G)) hsum
    simpa using hh

end SunTwoDeletion
