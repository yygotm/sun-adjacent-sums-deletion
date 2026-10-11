import SunThreeDeletion.ElementaryThree
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G]

theorem prime_hom_nonzero (p : ℕ) [Fact p.Prime] (d : G) (hd : d ≠ 0)
    (hp : p • d = 0) (x : ZMod p) (hx : x ≠ 0) :
    zmodSMulHom p d hp x ≠ 0 := by
  intro h
  have heq : x⁻¹.val • x = (1 : ZMod p) := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hx]
  have hh := congrArg (zmodSMulHom p d hp) heq
  rw [map_nsmul, h, smul_zero] at hh
  have h1 : zmodSMulHom p d hp 1 = d := by
    simpa using zmodSMulHom_nat p d hp 1
  exact hd (by rw [h1] at hh; exact hh.symm)

theorem prime_hom_injective (p : ℕ) [Fact p.Prime] (d : G) (hd : d ≠ 0)
    (hp : p • d = 0) : Function.Injective (zmodSMulHom p d hp) := by
  intro x y h
  by_contra hne
  exact prime_hom_nonzero p d hd hp (x-y) (sub_ne_zero.mpr hne)
    (by rw [map_sub,h,sub_self])

theorem prime_pair_coordinates (p : ℕ) [Fact p.Prime]
    (d r : G) (hd : d ≠ 0) (hdp : p • d=0) (hrp : p • r=0)
    (hr : r ∉ AddSubgroup.zmultiples d)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤) :
    ∃ e : (ZMod p × ZMod p) ≃+ G, e (1,0)=d ∧ e (0,1)=r := by
  let f := zmodSMulHom p d hdp
  let g := zmodSMulHom p r hrp
  have hf := prime_hom_injective p d hd hdp
  have hg (x : ZMod p) (hx : x ≠ 0) : g x ∉ AddSubgroup.zmultiples d := by
    intro hm
    have heq : x⁻¹.val • x = (1 : ZMod p) := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hx]
    have hh := congrArg g heq
    rw [map_nsmul] at hh
    have h1 : g 1 = r := by simpa using zmodSMulHom_nat p r hrp 1
    rw [h1] at hh
    exact hr (hh ▸ (AddSubgroup.zmultiples d).nsmul_mem hm _)
  let F : (ZMod p × ZMod p) →+ G := {
    toFun := fun x => f x.1+g x.2
    map_zero' := by simp
    map_add' := fun x y => by simp; abel
  }
  have hFi : Function.Injective F := by
    rintro ⟨i,j⟩ ⟨k,l⟩ h
    have hjl : j=l := by
      by_contra hjl
      apply hg (j-l) (sub_ne_zero.mpr hjl)
      have heq : g (j-l) = f (k-i) := by
        rw [map_sub,map_sub]
        change f i+g j=f k+g l at h
        exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using h)
      rw [heq]
      exact zmodSMulHom_mem p d hdp (k-i)
    subst l
    have hik : i=k := hf (add_right_cancel h)
    subst k
    rfl
  have hFs : Function.Surjective F := by
    intro x
    have hm : x ∈ AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r := by rw [hspan]; trivial
    obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp hm
    obtain ⟨i,hi⟩ := ha
    obtain ⟨j,hj⟩ := hb
    refine ⟨(i,j), ?_⟩
    change f (i : ZMod p)+g (j : ZMod p)=x
    rw [zmodSMulHom_int,zmodSMulHom_int]
    change i • d=a at hi
    change j • r=b at hj
    rw [hi,hj]
    exact hab
  let e := AddEquiv.ofBijective F ⟨hFi,hFs⟩
  refine ⟨e,?_,?_⟩
  · change f 1+g 0=d
    rw [map_zero,add_zero]
    simpa using zmodSMulHom_nat p d hdp 1
  · change f 0+g 1=r
    rw [map_zero,zero_add]
    simpa using zmodSMulHom_nat p r hrp 1

end SunThreeDeletion
