import SunThreeDeletion.Certificate
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
namespace SunFourDeletion

def zigIndex (l : ℕ) (j : Fin (2*l+1)) : Fin (2*l+1) :=
  if h0 : j.val = 0 then ⟨0,by omega⟩
  else if he : j.val % 2 = 0 then ⟨2*l+1-j.val/2,by have := j.isLt; omega⟩
  else ⟨l-j.val/2,by have := j.isLt; omega⟩

theorem zigIndex_injective (l : ℕ) : Function.Injective (zigIndex l) := by
  intro i j hij
  have h := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  simp only [zigIndex] at h
  split_ifs at h <;> dsimp at h <;> omega

theorem zigIndex_val (l : ℕ) (j : Fin (2*l+1)) :
    (zigIndex l j).val = if j.val=0 then 0 else
      if j.val % 2=0 then 2*l+1-j.val/2 else l-j.val/2 := by
  unfold zigIndex
  split_ifs <;> rfl

def colorIndex (l : ℕ) (j : Fin (2*l+1)) : Fin (2*l+1) :=
  if h0 : j.val = 0 then ⟨0,by omega⟩ else ⟨2*l+1-j.val,by have := j.isLt; omega⟩

theorem colorIndex_injective (l : ℕ) : Function.Injective (colorIndex l) := by
  intro i j hij
  have h := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  simp only [colorIndex] at h
  split_ifs at h <;> dsimp at h <;> omega

theorem colorIndex_val (l : ℕ) (j : Fin (2*l+1)) :
    (colorIndex l j).val = if j.val=0 then 0 else 2*l+1-j.val := by
  unfold colorIndex
  split_ifs <;> rfl

def lowIndex (l : ℕ) (i : Fin (2*l+1)) : Fin (2*l+1) :=
  ⟨i.val/2,by have := i.isLt; omega⟩

def highIndex (l : ℕ) (i : Fin (2*l+1)) : Fin (2*l+1) :=
  ⟨l+(i.val+1)/2,by have := i.isLt; omega⟩

theorem zig_pair (l : ℕ) (hl : 1 ≤ l) (i : Fin (2*l+1)) :
    (zigIndex l i = lowIndex l (colorIndex l i) ∧
      zigIndex l (finRotate (2*l+1) i) = highIndex l (colorIndex l i)) ∨
    (zigIndex l i = highIndex l (colorIndex l i) ∧
      zigIndex l (finRotate (2*l+1) i) = lowIndex l (colorIndex l i)) := by
  have hi := i.isLt
  have hr : (finRotate (2*l+1) i).val = (i.val+1) % (2*l+1) := by
    rw [finRotate_apply, Fin.val_add]
    change (i.val + 1 % (2*l+1)) % (2*l+1) = _
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2*l+1)]
  by_cases h0 : i.val = 0
  · left
    constructor <;> apply Fin.ext <;>
      simp only [zigIndex_val,lowIndex,highIndex,colorIndex_val,hr,h0,
        Nat.mod_eq_of_lt (by omega : 1 < 2*l+1)] <;> simp
  by_cases he : i.val % 2 = 0
  · right
    constructor <;> apply Fin.ext
    · simp only [zigIndex_val,highIndex,colorIndex_val,h0,↓reduceIte,he]
      omega
    · simp only [zigIndex_val,lowIndex,colorIndex_val,h0,↓reduceIte,hr]
      by_cases hh : i.val+1 < 2*l+1
      · simp only [Nat.mod_eq_of_lt hh]
        clear hr
        split_ifs <;> first | contradiction | omega
      · have hh' : i.val+1=2*l+1 := by omega
        simp only [hh',Nat.mod_self]
        simp only [↓reduceIte]
        omega
  · left
    constructor <;> apply Fin.ext
    · simp only [zigIndex_val,lowIndex,colorIndex_val,h0,↓reduceIte,he]
      omega
    · simp only [zigIndex_val,highIndex,colorIndex_val,h0,↓reduceIte,hr]
      have hh : i.val+1 < 2*l+1 := by omega
      simp only [Nat.mod_eq_of_lt hh]
      clear hr
      split_ifs <;> first | contradiction | omega

end SunFourDeletion
