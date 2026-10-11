import SunThreeDeletion.QBoundary

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace SunThreeDeletion

/-- Four consecutive positions, with the middle two equal to the desired holes. -/
def FourRun (v : ℕ → ℕ) (n t : ℕ) : Prop :=
  ∃ j, j+3<n ∧
    ((v (j+1) = t ∧ v (j+2) = t+2) ∨ (v (j+1) = t+2 ∧ v (j+2) = t)) ∧
    v j + v (j+3) = v (j+1) + v (j+2)

theorem interior1_four_run (k t : ℕ) (hk : 12 ≤ k) (ht : Interior1 k t) :
    FourRun (q1Vertex k) (4*k) t := by
  rcases ht with h | h | h | h
  · refine ⟨(t-2*k-4)/2, ?_⟩
    simp only [q1Vertex]
    split_ifs <;> omega
  · refine ⟨k+(t-4)/2, ?_⟩
    simp only [q1Vertex]
    split_ifs <;> omega
  · refine ⟨2*k+(2*k-t-5)/2, ?_⟩
    simp only [q1Vertex]
    split_ifs <;> omega
  · refine ⟨3*k+(4*k-t-5)/2, ?_⟩
    simp only [q1Vertex]
    split_ifs <;> omega

theorem interior3_four_run (k t : ℕ) (hk : 12 ≤ k) (ht : Interior3 k t) :
    FourRun (q3Vertex k) (4*k+2) t := by
  rcases ht with h | h | h | h
  · refine ⟨(t-2*k-4)/2, ?_⟩
    simp only [q3Vertex]
    split_ifs <;> omega
  · refine ⟨k+1+(t-4)/2, ?_⟩
    simp only [q3Vertex]
    split_ifs <;> omega
  · refine ⟨2*k+1+(2*k-t-3)/2, ?_⟩
    simp only [q3Vertex]
    split_ifs <;> omega
  · refine ⟨3*k+2+(4*k-t-3)/2, ?_⟩
    simp only [q3Vertex]
    split_ifs <;> omega

end SunThreeDeletion

