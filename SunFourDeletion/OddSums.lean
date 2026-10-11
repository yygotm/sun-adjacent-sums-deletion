import SunFourDeletion.OddIndices

set_option autoImplicit false
namespace SunFourDeletion

def sortedSum (l : ℕ) (a : Fin (2*l+1) → ℕ) (i : Fin (2*l+1)) : ℕ :=
  a (lowIndex l i) + a (highIndex l i)

theorem sortedSum_strictMono (l : ℕ) (a : Fin (2*l+1) → ℕ) (ha : StrictMono a) :
    StrictMono (sortedSum l a) := by
  intro i j hij
  have hv : i.val < j.val := hij
  have hl : lowIndex l i ≤ lowIndex l j := by change i.val/2 ≤ j.val/2; omega
  have hh : highIndex l i ≤ highIndex l j := by
    change l+(i.val+1)/2 ≤ l+(j.val+1)/2
    omega
  have hla := ha.monotone hl
  have hha := ha.monotone hh
  rcases lt_or_eq_of_le hl with hlt | heq
  · have := ha hlt
    unfold sortedSum
    omega
  · have he := congrArg Fin.val heq
    have hlt : highIndex l i < highIndex l j := by
      change l+(i.val+1)/2 < l+(j.val+1)/2
      change i.val/2 = j.val/2 at he
      omega
    have := ha hlt
    unfold sortedSum
    omega

theorem sortedSum_bounds (l : ℕ) (a : Fin (2*l+1) → ℕ) (ha : StrictMono a)
    (i : Fin (2*l+1)) :
    a ⟨0,by omega⟩ + a ⟨l,by omega⟩ ≤ sortedSum l a i ∧
    sortedSum l a i ≤ a ⟨l,by omega⟩ + a ⟨2*l,by omega⟩ := by
  have hi := i.isLt
  have h1 := ha.monotone (show (⟨0,by omega⟩ : Fin (2*l+1)) ≤ lowIndex l i from by
    change 0 ≤ i.val/2; omega)
  have h2 := ha.monotone (show (⟨l,by omega⟩ : Fin (2*l+1)) ≤ highIndex l i from by
    change l ≤ l+(i.val+1)/2; omega)
  have h3 := ha.monotone (show lowIndex l i ≤ (⟨l,by omega⟩ : Fin (2*l+1)) from by
    change i.val/2 ≤ l; omega)
  have h4 := ha.monotone (show highIndex l i ≤ (⟨2*l,by omega⟩ : Fin (2*l+1)) from by
    change l+(i.val+1)/2 ≤ 2*l; omega)
  unfold sortedSum
  omega

theorem natCast_eq_of_interval (M b t x y : ℕ) [NeZero M]
    (hbx : b≤x) (hby : b≤y) (hxt : x≤t) (hyt : y≤t) (hwidth : t-b<M)
    (he : (x : ZMod M) = (y : ZMod M)) : x=y := by
  have hx : x-b<M := by omega
  have hy : y-b<M := by omega
  have hd : ((x-b : ℕ) : ZMod M) = ((y-b : ℕ) : ZMod M) := by
    rw [Nat.cast_sub hbx,Nat.cast_sub hby,he]
  have hh := congrArg ZMod.val hd
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at hh
  omega

theorem sortedSum_cast_injective (M l : ℕ) [NeZero M]
    (a : Fin (2*l+1) → ℕ) (ha : StrictMono a) (hb : ∀ i, a i<M) :
    Function.Injective (fun i => (sortedSum l a i : ZMod M)) := by
  intro i j he
  have hi := sortedSum_bounds l a ha i
  have hj := sortedSum_bounds l a ha j
  have ht := hb ⟨2*l,by omega⟩
  have hw : (a ⟨l,by omega⟩ + a ⟨2*l,by omega⟩) -
      (a ⟨0,by omega⟩ + a ⟨l,by omega⟩) < M := by omega
  exact (sortedSum_strictMono l a ha).injective
    (natCast_eq_of_interval M _ _ _ _ hi.1 hj.1 hi.2 hj.2 hw he)

theorem zig_sum (l : ℕ) (hl : 1≤l) (a : Fin (2*l+1) → ℕ)
    (i : Fin (2*l+1)) :
    a (zigIndex l i) + a (zigIndex l (finRotate (2*l+1) i)) =
      sortedSum l a (colorIndex l i) := by
  rcases zig_pair l hl i with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simp only [h1,h2,sortedSum]
  · simp only [h1,h2,sortedSum,add_comm]

end SunFourDeletion
