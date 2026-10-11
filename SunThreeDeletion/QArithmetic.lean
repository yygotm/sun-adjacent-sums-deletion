import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace SunThreeDeletion

/-- Natural representatives of Q_(4k+1), indexed starting at zero. -/
def q1Vertex (k j : ℕ) : ℕ :=
  if j < k then 2*k+2+2*j
  else if j < 2*k then 2*(j-k)+2
  else if j < 3*k then 2*k-1-2*(j-2*k)
  else 4*k-1-2*(j-3*k)

/-- The representatives of the edge sums, including each of the four seams. -/
def q1Color (k j : ℕ) : ℕ :=
  if j < k then (if j+1 < k then 5+4*j else 1)
  else if j < 2*k then (if j+1 < 2*k then 6+4*(j-k) else 4*k-1)
  else if j < 3*k then (if j+1 < 3*k then 4*k-4-4*(j-2*k) else 4*k)
  else (if j+1 < 4*k then 4*k-5-4*(j-3*k) else 2)

def q3Vertex (k j : ℕ) : ℕ :=
  if j < k+1 then 2*k+2+2*j
  else if j < 2*k+1 then 2*(j-(k+1))+2
  else if j < 3*k+2 then 2*k+1-2*(j-(2*k+1))
  else 4*k+1-2*(j-(3*k+2))

def q3Color (k j : ℕ) : ℕ :=
  if j < k+1 then (if j+1 < k+1 then 3+4*j else 1)
  else if j < 2*k+1 then (if j+1 < 2*k+1 then 6+4*(j-(k+1)) else 4*k+1)
  else if j < 3*k+2 then (if j+1 < 3*k+2 then 4*k-4*(j-(2*k+1)) else 4*k+2)
  else (if j+1 < 4*k+2 then 4*k-3-4*(j-(3*k+2)) else 2)

theorem q1Vertex_bounds (k j : ℕ) (hk : 0 < k) (hj : j < 4*k) :
    0 < q1Vertex k j ∧ q1Vertex k j < 4*k+1 := by
  unfold q1Vertex
  split_ifs <;> omega

theorem q1Vertex_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun j : Fin (4*k) => q1Vertex k j.val) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [q1Vertex] at h
  split_ifs at h <;> omega

theorem q1Color_bounds (k j : ℕ) (hk : 0 < k) (hj : j < 4*k) :
    0 < q1Color k j ∧ q1Color k j < 4*k+1 := by
  unfold q1Color
  split_ifs <;> omega

theorem q1Color_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun j : Fin (4*k) => q1Color k j.val) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [q1Color] at h
  split_ifs at h <;> omega

theorem q1_sum (k j : ℕ) (hk : 0 < k) (hj : j < 4*k) :
    q1Vertex k j + q1Vertex k (if j+1 < 4*k then j+1 else 0) =
      q1Color k j ∨
    q1Vertex k j + q1Vertex k (if j+1 < 4*k then j+1 else 0) =
      q1Color k j + (4*k+1) := by
  simp only [q1Vertex, q1Color]
  split_ifs <;> omega

theorem q3Vertex_bounds (k j : ℕ) (hk : 0 < k) (hj : j < 4*k+2) :
    0 < q3Vertex k j ∧ q3Vertex k j < 4*k+3 := by
  unfold q3Vertex
  split_ifs <;> omega

theorem q3Vertex_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun j : Fin (4*k+2) => q3Vertex k j.val) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [q3Vertex] at h
  split_ifs at h <;> omega

theorem q3Color_bounds (k j : ℕ) (hk : 0 < k) (hj : j < 4*k+2) :
    0 < q3Color k j ∧ q3Color k j < 4*k+3 := by
  unfold q3Color
  split_ifs <;> omega

theorem q3Color_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun j : Fin (4*k+2) => q3Color k j.val) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [q3Color] at h
  split_ifs at h <;> omega

theorem q3_sum (k j : ℕ) (hk : 0 < k) (hj : j < 4*k+2) :
    q3Vertex k j + q3Vertex k (if j+1 < 4*k+2 then j+1 else 0) =
      q3Color k j ∨
    q3Vertex k j + q3Vertex k (if j+1 < 4*k+2 then j+1 else 0) =
      q3Color k j + (4*k+3) := by
  simp only [q3Vertex, q3Color]
  split_ifs <;> omega

end SunThreeDeletion

