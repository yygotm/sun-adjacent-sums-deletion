import SunThreeDeletion.QCycle
import SunThreeDeletion.SeparatedSurgery

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

def specialNat (m : ℕ) : Fin 6 → ℕ := ![m-3, m-1, 2, 3, 1, m-2]

theorem specialNat_bounds (m : ℕ) (hm : 7 ≤ m) (i : Fin 6) :
    0 < specialNat m i ∧ specialNat m i < m := by
  fin_cases i <;> simp [specialNat] <;> omega

theorem specialNat_injective (m : ℕ) (hm : 7 ≤ m) :
    Function.Injective (specialNat m) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [specialNat] at h ⊢ <;> omega

def specialEmbedding (m : ℕ) (hm : 7 ≤ m) : Fin 6 ↪ ZMod m :=
  ⟨fun i => (specialNat m i : ZMod m),
    natCast_injective_of_bounds _ (fun i => (specialNat_bounds m hm i).2)
      (specialNat_injective m hm)⟩

theorem special_deletion (m : ℕ) (hm : 7 ≤ m)
    (C : RainbowCycle ({0}ᶜ : Set (ZMod m))) (hzero : C.next 0 = 0)
    (h1 : C.next ((m-3 : ℕ) : ZMod m) = ((m-1 : ℕ) : ZMod m))
    (h2 : C.next ((m-1 : ℕ) : ZMod m) = 2)
    (h3 : C.next 3 = 1)
    (h4 : C.next 1 = ((m-2 : ℕ) : ZMod m)) :
    HasRainbowCycle ({0, ((m-1 : ℕ) : ZMod m), 1}ᶜ : Set (ZMod m)) := by
  let e := specialEmbedding m hm
  have he (i : Fin 6) : e i ∈ ({0}ᶜ : Set (ZMod m)) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hv := congrArg ZMod.val h
    change (specialNat m i : ZMod m).val = (0 : ZMod m).val at hv
    rw [ZMod.val_natCast_of_lt (specialNat_bounds m hm i).2, ZMod.val_zero] at hv
    have := (specialNat_bounds m hm i).1
    omega
  have hnt : ({0}ᶜ : Set (ZMod m)).Nontrivial :=
    ⟨e 0, he 0, e 1, he 1, e.injective.ne (by decide)⟩
  have hsupp (z : ZMod m) : C.next z ≠ z ↔ z ∈ ({0}ᶜ : Set (ZMod m)) := by
    by_cases hz : z = 0
    · simp [hz, hzero]
    · have hz' : z ∈ ({0}ᶜ : Set (ZMod m)) := by simpa using hz
      exact iff_of_true (C.cyclic.apply_ne hnt hz') hz'
  have hp : C.next.IsCycle :=
    Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨_, hnt, C.cyclic, fun z hz => (hsupp z).mp hz⟩
  have h := delete_separated C hp hsupp e
    (by simpa [e, specialEmbedding, specialNat] using h1)
    (by simpa [e, specialEmbedding, specialNat] using h2)
    (by simpa [e, specialEmbedding, specialNat] using h3)
    (by simpa [e, specialEmbedding, specialNat] using h4)
    (by
      have hh : m-3+2 = 1+(m-2) := by omega
      simpa [e, specialEmbedding, specialNat, Nat.cast_add] using
        congrArg (fun z : ℕ => (z : ZMod m)) hh)
    (by
      have hh : 3+(m-2) = m-1+2 := by omega
      simpa [e, specialEmbedding, specialNat, Nat.cast_add] using
        congrArg (fun z : ℕ => (z : ZMod m)) hh)
  have hset :
      ({0}ᶜ : Set (ZMod m)) \ {e 1, e 4} =
      ({0, ((m-1 : ℕ) : ZMod m), 1}ᶜ : Set (ZMod m)) := by
    ext z
    simp [e, specialEmbedding, specialNat, and_assoc]
  rwa [hset] at h

theorem q1_special_values (k : ℕ) (hk : 12 ≤ k) :
    q1Vertex k (k-2) = 4*k-2 ∧ q1Vertex k (k-1) = 4*k ∧ q1Vertex k k = 2 ∧
    q1Vertex k (3*k-2) = 3 ∧ q1Vertex k (3*k-1) = 1 ∧ q1Vertex k (3*k) = 4*k-1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [q1Vertex] <;> split_ifs <;> omega

theorem q3_special_values (k : ℕ) (hk : 12 ≤ k) :
    q3Vertex k (k-1) = 4*k ∧ q3Vertex k k = 4*k+2 ∧ q3Vertex k (k+1) = 2 ∧
    q3Vertex k (3*k) = 3 ∧ q3Vertex k (3*k+1) = 1 ∧ q3Vertex k (3*k+2) = 4*k+1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [q3Vertex] <;> split_ifs <;> omega

end SunThreeDeletion

