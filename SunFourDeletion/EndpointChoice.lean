import SunFourDeletion.Avoidance
import SunThreeDeletion.Orient

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

def prefixPerm {H : Type*} (f : ℕ → Equiv.Perm H) : ℕ → Equiv.Perm H
  | 0 => 1
  | n+1 => f n * prefixPerm f n

theorem cycle_chain_endpoints {H : Type*} [AddCommGroup H] [Fintype H]
    (m : ℕ) (hm : 0<m) (D : Fin m → Finset H)
    (C : ∀ i, RainbowCycle ((D i : Set H)ᶜ))
    (hsize : ∀ i, 3 ≤ Nat.card {x : H // x ∉ D i})
    (hsmall : (∑ i, (D i).card) < Fintype.card H) (c : H) :
    ∃ z : ℕ → H, z m ≠ z 0-c ∧
      ∀ i : Fin m, ∃ P : RainbowCycle ((D i : Set H)ᶜ),
        z i.val ∈ (D i : Set H)ᶜ ∧ z (i.val+1) ∈ (D i : Set H)ᶜ ∧
        P.next (z (i.val+1)) = z i.val := by
  classical
  let f : ℕ → Equiv.Perm H := fun n =>
    if hn : n<m then (C ⟨n,hn⟩).next.symm else 1
  obtain ⟨u,hu⟩ := exists_avoiding_permutations D (fun i => prefixPerm f i.val) hsmall
  let j : Fin m := ⟨m-1,by omega⟩
  have huj : prefixPerm f (m-1) u ∈ (D j : Set H)ᶜ := hu j
  obtain ⟨P,w,hw,hnext,hwne⟩ := predecessor_avoiding (C j) (hsize j)
    (prefixPerm f (m-1) u) huj (u-c)
  let z : ℕ → H := fun n => if n=m then w else prefixPerm f n u
  have hz (n : ℕ) (hn : n<m) : z n = prefixPerm f n u := if_neg (Nat.ne_of_lt hn)
  have hz0 : z 0=u := by rw [hz 0 hm]; rfl
  have hzm : z m=w := by simp [z]
  refine ⟨z,?_,?_⟩
  · rwa [hzm,hz0]
  · intro i
    have hstart : z i.val ∈ (D i : Set H)ᶜ := by rw [hz i.val i.isLt]; exact hu i
    by_cases hi : i.val+1=m
    · have hij : i=j := Fin.ext (by dsimp [j]; omega)
      subst i
      refine ⟨P,hstart,?_,?_⟩
      · rw [hi,hzm]
        exact hw
      · rw [hi,hzm,hz j.val j.isLt]
        exact hnext
    · have hi' : i.val+1<m := by have := i.isLt; omega
      have hstep : z (i.val+1) = (C i).next.symm (z i.val) := by
        rw [hz (i.val+1) hi',hz i.val i.isLt]
        simp only [prefixPerm,Equiv.Perm.mul_apply,f,dif_pos i.isLt]
      refine ⟨C i,hstart,?_,?_⟩
      · rw [hstep]
        exact (C i).cyclic.inv.1.mapsTo hstart
      · rw [hstep]
        exact (C i).next.apply_symm_apply _

end SunFourDeletion
