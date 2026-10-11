import SunTwoDeletion.Cyclic
import SunTwoDeletion.Linearize

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def orbitEquiv (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) : Fin (Fintype.card G) ≃ G := by
  classical
  let g := generatorCycle hodd r hgen
  let c : RainbowCycle ((Finset.univ : Finset G) : Set G) :=
    ⟨g.next, by simpa using g.cyclic, by simpa using g.rainbow⟩
  let v := cycleEmbedding (s := Finset.univ) c (0 : G) (Finset.mem_univ 0)
  have hv : Function.Surjective v := by
    apply Set.range_eq_univ.mp
    simpa using cycleEmbedding_range c (0 : G) (Finset.mem_univ 0)
  exact Equiv.ofBijective v ⟨v.injective, hv⟩

theorem orbitEquiv_apply (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) (i : Fin (Fintype.card G)) :
    orbitEquiv hodd r hgen i = i.val • r := by
  change ((Equiv.addRight r) ^ i.val) 0 = _
  rw [Equiv.nsmul_addRight]
  change 0 + i.val • r = _
  exact zero_add _

theorem orbitEquiv_zero (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) (hcard : 0 < Fintype.card G) :
    orbitEquiv hodd r hgen ⟨0, hcard⟩ = 0 := by
  rw [orbitEquiv_apply]
  exact zero_nsmul _

theorem orbitEquiv_succ (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) (i : Fin (Fintype.card G))
    (hi : i.val + 1 < Fintype.card G) :
    orbitEquiv hodd r hgen ⟨i.val + 1, hi⟩ = orbitEquiv hodd r hgen i + r := by
  rw [orbitEquiv_apply, orbitEquiv_apply]
  exact succ_nsmul _ _

theorem orbitEquiv_last (hodd : Odd (Nat.card G)) (r : G)
    (hgen : ∀ z : G, z ∈ AddSubgroup.zmultiples r) (i : Fin (Fintype.card G))
    (hi : ¬i.val + 1 < Fintype.card G) :
    orbitEquiv hodd r hgen i + r = 0 := by
  have hcard : i.val + 1 = Fintype.card G := by have := i.isLt; omega
  rw [orbitEquiv_apply, ← succ_nsmul, hcard]
  exact card_nsmul_eq_zero

end SunTwoDeletion
