import SunTwoDeletion.Basic
import SunTwoDeletion.Algebra
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

def generatorCycle (hodd : Odd (Nat.card G)) (d : G)
    (hd : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    RainbowCycle (Set.univ : Set G) where
  next := Equiv.addRight d
  cyclic := by
    refine ⟨(Equiv.addRight d).bijective.bijOn_univ, ?_⟩
    intro x _ y _
    obtain ⟨n, hn⟩ := hd (y - x)
    refine ⟨n, ?_⟩
    rw [Equiv.zsmul_addRight]
    change x + n • d = y
    change n • d = y - x at hn
    rw [hn]
    abel
  rainbow := by
    intro x _ y _ h
    apply double_injective hodd
    change x + (x + d) = y + (y + d) at h
    simpa only [← add_assoc, add_left_inj] using h

theorem generatorCycle_edge (hodd : Odd (Nat.card G)) (d : G)
    (hd : ∀ x : G, x ∈ AddSubgroup.zmultiples d) :
    (generatorCycle hodd d hd).next 0 = d := by
  simp [generatorCycle]

theorem prime_edge_property (hodd : Odd (Nat.card G)) (hp : (Nat.card G).Prime) :
    EdgeProperty G := by
  letI : Fact (Nat.card G).Prime := ⟨hp⟩
  intro u v huv
  have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  let c := generatorCycle hodd (v - u) (fun _ => mem_zmultiples_of_prime_card rfl hd)
  refine ⟨c, ?_⟩
  change u + (v - u) = v
  abel

end SunTwoDeletion
