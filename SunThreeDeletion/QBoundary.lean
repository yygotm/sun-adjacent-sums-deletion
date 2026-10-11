import SunThreeDeletion.QArithmetic

set_option autoImplicit false
namespace SunThreeDeletion

/-- The two deleted values and both outside neighbours lie in one step-two run. -/
def Interior1 (k t : ℕ) : Prop :=
  (t % 2 = 0 ∧ 2*k+4 ≤ t ∧ t+4 ≤ 4*k) ∨
  (t % 2 = 0 ∧ 4 ≤ t ∧ t+4 ≤ 2*k) ∨
  (t % 2 = 1 ∧ 3 ≤ t ∧ t+4 ≤ 2*k-1) ∨
  (t % 2 = 1 ∧ 2*k+3 ≤ t ∧ t+4 ≤ 4*k-1)

def Interior3 (k t : ℕ) : Prop :=
  (t % 2 = 0 ∧ 2*k+4 ≤ t ∧ t+4 ≤ 4*k+2) ∨
  (t % 2 = 0 ∧ 4 ≤ t ∧ t+4 ≤ 2*k) ∨
  (t % 2 = 1 ∧ 3 ≤ t ∧ t+4 ≤ 2*k+1) ∨
  (t % 2 = 1 ∧ 2*k+5 ≤ t ∧ t+4 ≤ 4*k+1)

def Boundary1 (k t : ℕ) : Prop :=
  t = 1 ∨ t = 2 ∨ t = 2*k-3 ∨ t = 2*k-2 ∨ t = 2*k-1 ∨
  t = 2*k ∨ t = 2*k+1 ∨ t = 2*k+2 ∨ t = 4*k-3 ∨ t = 4*k-2 ∨ t = 4*k

def Boundary3 (k t : ℕ) : Prop :=
  t = 1 ∨ t = 2 ∨ t = 2*k-2 ∨ t = 2*k-1 ∨ t = 2*k ∨
  t = 2*k+1 ∨ t = 2*k+2 ∨ t = 2*k+3 ∨ t = 4*k-1 ∨ t = 4*k ∨ t = 4*k+2

/-- This derives the exceptional table from run endpoint inequalities. -/
theorem boundary1_of_not_interior (k t : ℕ) (hk : 12 ≤ k)
    (ht : 0 < t) (hlt : t < 4*k+1) (hnz : t ≠ 4*k-1)
    (h : ¬ Interior1 k t) : Boundary1 k t := by
  simp only [Interior1, Boundary1] at *
  omega

theorem boundary3_of_not_interior (k t : ℕ) (hk : 12 ≤ k)
    (ht : 0 < t) (hlt : t < 4*k+3) (hnz : t ≠ 4*k+1)
    (h : ¬ Interior3 k t) : Boundary3 k t := by
  simp only [Interior3, Boundary3] at *
  omega

def BadRepresentative (s : ℤ) : Prop :=
  s = -8 ∨ s = -7 ∨ s = -6 ∨ s = -5 ∨ s = -3 ∨ s = -1 ∨
  s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4

/-- All boundary cases except the valid deletion {-1,1} have a small doubled residue. -/
theorem boundary1_small_double (k t : ℕ) (hk : 12 ≤ k)
    (h : Boundary1 k t) (hex : t ≠ 4*k) :
    ∃ s : ℤ, BadRepresentative s ∧ (4*(k : ℤ)+1) ∣ (2*(t : ℤ)-s) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨2, by simp [BadRepresentative], by rw [h]; norm_num⟩
  · exact ⟨4, by simp [BadRepresentative], by rw [h]; norm_num⟩
  · refine ⟨-7, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-5, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-3, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-1, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨1, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨3, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-8, by simp [BadRepresentative], ⟨2, ?_⟩⟩; omega
  · refine ⟨-6, by simp [BadRepresentative], ⟨2, ?_⟩⟩; omega
  · exact (hex h).elim

theorem boundary3_small_double (k t : ℕ) (hk : 12 ≤ k)
    (h : Boundary3 k t) (hex : t ≠ 4*k+2) :
    ∃ s : ℤ, BadRepresentative s ∧ (4*(k : ℤ)+3) ∣ (2*(t : ℤ)-s) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨2, by simp [BadRepresentative], by rw [h]; norm_num⟩
  · exact ⟨4, by simp [BadRepresentative], by rw [h]; norm_num⟩
  · refine ⟨-7, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-5, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-3, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-1, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨1, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨3, by simp [BadRepresentative], ⟨1, ?_⟩⟩; omega
  · refine ⟨-8, by simp [BadRepresentative], ⟨2, ?_⟩⟩; omega
  · refine ⟨-6, by simp [BadRepresentative], ⟨2, ?_⟩⟩; omega
  · exact (hex h).elim

end SunThreeDeletion

