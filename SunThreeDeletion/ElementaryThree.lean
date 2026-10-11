import SunThreeDeletion.SmallCases
import SunThreeDeletion.AffineTemplates
import SunTwoDeletion.Algebra
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G]

def zmodSMulHom (n : ℕ) (d : G) (h : n • d = 0) : ZMod n →+ G :=
  ZMod.lift n ⟨zmultiplesHom G d, by simpa using h⟩

theorem zmodSMulHom_nat (n : ℕ) (d : G) (h : n • d = 0) (k : ℕ) :
    zmodSMulHom n d h k = k • d := by
  let F : {f : ℤ →+ G // f n=0} := ⟨zmultiplesHom G d, by simpa using h⟩
  have hh := ZMod.lift_coe n F (k : ℤ)
  change ZMod.lift n F ((k : ℤ) : ZMod n) = (k : ℤ) • d at hh
  simpa only [zmodSMulHom,F,Int.cast_natCast,natCast_zsmul] using hh

theorem zmodSMulHom_int (n : ℕ) (d : G) (h : n • d = 0) (k : ℤ) :
    zmodSMulHom n d h k = k • d := by
  change ZMod.lift n ⟨zmultiplesHom G d, _⟩ k = _
  rw [ZMod.lift_coe]
  rfl

theorem zmodSMulHom_val (n : ℕ) [NeZero n] (d : G) (h : n • d = 0) (x : ZMod n) :
    zmodSMulHom n d h x = x.val • d := by
  have hh := zmodSMulHom_nat n d h x.val
  rwa [ZMod.natCast_zmod_val] at hh

theorem zmodSMulHom_mem (n : ℕ) [NeZero n] (d : G) (h : n • d = 0) (x : ZMod n) :
    zmodSMulHom n d h x ∈ AddSubgroup.zmultiples d := by
  rw [zmodSMulHom_val]
  exact (AddSubgroup.zmultiples d).nsmul_mem (AddSubgroup.mem_zmultiples d) _

theorem three_hom_injective (hodd : Odd (Nat.card G)) (d : G) (hd : d ≠ 0) (h3 : 3 • d = 0) :
    Function.Injective (zmodSMulHom 3 d h3) := by
  have hker (x : ZMod 3) (hx : zmodSMulHom 3 d h3 x = 0) : x=0 := by
    rw [zmodSMulHom_val] at hx
    fin_cases x
    · rfl
    · exact (hd (by simpa [ZMod.val] using hx)).elim
    · exact (hd (double_injective hodd (by simpa [ZMod.val,two_nsmul] using hx))).elim
  intro x y h
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub,h,sub_self]

/-- If d,r have order three and r is outside <d>, their generated subgroup has
the explicit C3 x C3 coordinates needed by the finite base. -/
theorem independent_three_cycle (hodd : Odd (Nat.card G))
    (d r : G) (hd : d ≠ 0) (hd3 : 3 • d=0) (hr3 : 3 • r=0)
    (hr : r ∉ AddSubgroup.zmultiples d)
    (hspan : AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r = ⊤) :
    HasRainbowCycle ({0,d,r}ᶜ : Set G) := by
  let f := zmodSMulHom 3 d hd3
  let g := zmodSMulHom 3 r hr3
  have hf := three_hom_injective hodd d hd hd3
  have hg (x : ZMod 3) (hx : x ≠ 0) : g x ∉ AddSubgroup.zmultiples d := by
    rw [zmodSMulHom_val]
    fin_cases x
    · exact (hx rfl).elim
    · simpa [ZMod.val] using hr
    · intro h
      apply hr
      have heq : r = -(2 • r) := by
        apply eq_neg_iff_add_eq_zero.mpr
        simpa [succ_nsmul,add_comm] using hr3
      rw [heq]
      exact (AddSubgroup.zmultiples d).neg_mem (by simpa [ZMod.val] using h)
  let F : (ZMod 3 × ZMod 3) →+ G := {
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
      exact zmodSMulHom_mem 3 d hd3 (k-i)
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
    change f (i : ZMod 3)+g (j : ZMod 3)=x
    rw [zmodSMulHom_int,zmodSMulHom_int]
    change i • d=a at hi
    change j • r=b at hj
    rw [hi,hj]
    exact hab
  let e := AddEquiv.ofBijective F ⟨hFi,hFs⟩
  have hh := affine_three_cycle e 0 (0,0) (1,0) (0,1) base_C3xC3_independent
  have he1 : e (1,0)=d := by
    change f 1+g 0=d
    rw [map_zero,add_zero]
    simpa using zmodSMulHom_nat 3 d hd3 1
  have he2 : e (0,1)=r := by
    change f 0+g 1=r
    rw [map_zero,zero_add]
    simpa using zmodSMulHom_nat 3 r hr3 1
  have he0 : e (0,0)=0 := e.map_zero
  simpa only [he0,zero_add,add_zero,he1,he2] using hh

end SunThreeDeletion

