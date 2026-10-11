import SunThreeDeletion.PrefixGlue
import SunThreeDeletion.MappedPaths
import SunThreeDeletion.Fibers

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Three holes in three consecutive generating cosets. -/
theorem three_punctured_fibers (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3 ≤ Nat.card H) (hq : 5 ≤ Nat.card (G ⧸ H)) (r : G)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (C : RainbowCycle ({0}ᶜ : Set H)) :
    HasRainbowCycle ({0,r,2 • r}ᶜ : Set G) := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨u,_,hu,_,_⟩ := exists_two_nonzero
    (by simpa only [Nat.card_eq_fintype_card] using hH) (0 : H)
  have hum : u ∈ ({0}ᶜ : Set H) := by simpa using hu
  let v0 := C.next⁻¹ u
  let v1 := C.next⁻¹ v0
  let v2 := C.next⁻¹ v1
  have hv0 : v0 ∈ ({0}ᶜ : Set H) := C.cyclic.inv.1.mapsTo hum
  have hv1 : v1 ∈ ({0}ᶜ : Set H) := C.cyclic.inv.1.mapsTo hv0
  have hv2 : v2 ∈ ({0}ᶜ : Set H) := C.cyclic.inv.1.mapsTo hv1
  let q := Nat.card (G ⧸ H)
  let R : G ⧸ H := QuotientAddGroup.mk r
  let e := natOrbit (quotient_odd hodd H) R hgen
  let s : Fin 3 → G := fun i => i.val • r
  let D := Set.range s
  let A := deletedFiber H e D
  let pre : List H := [v0-u,v1-v0,v2-v1]
  let ε : ℕ → G := fun i => (pre.getD i 0 : G)
  let i0 : Fin q := ⟨0,by omega⟩
  let i1 : Fin q := ⟨1,by omega⟩
  let i2 : Fin q := ⟨2,by omega⟩
  have hs (i : Fin 3) :
      (QuotientAddGroup.mk (s i) : G ⧸ H) = e ⟨i.val,by have := i.isLt; omega⟩ := by
    change (QuotientAddGroup.mk' H) (i.val • r) = _
    rw [map_nsmul,natOrbit_apply]
    rfl
  have hA : ∀ j z, z ∈ A j →
      (QuotientAddGroup.mk z : G ⧸ H) = j.val • (QuotientAddGroup.mk r : G ⧸ H) := by
    intro j z hz
    exact hz.1.trans (natOrbit_apply (quotient_odd hodd H) R hgen j)
  have hD : ∀ z ∈ D, ∃ i : Fin q, i.val<3 ∧ (QuotientAddGroup.mk z : G ⧸ H) = e i := by
    rintro z ⟨i,rfl⟩
    exact ⟨⟨i.val,by have := i.isLt; omega⟩, i.isLt, hs i⟩
  have hfull (j : Fin q) (hj : pre.length ≤ j.val) :
      A j = {z | (QuotientAddGroup.mk z : G ⧸ H) = j.val • R} := by
    change deletedFiber H e D j = _
    rw [deletedFiber_full H e D 3 hD j (by simpa [pre] using hj)]
    rw [natOrbit_apply]
  have hA0 : A i0 = (fun x : H => (x : G)+0) '' ({0}ᶜ : Set H) := by
    simpa [s,i0] using fiber_one_hole H e 3 (by omega) s hs (0 : Fin 3)
  have hA1 : A i1 = (fun x : H => (x : G)+r) '' ({0}ᶜ : Set H) := by
    simpa [s,i1] using fiber_one_hole H e 3 (by omega) s hs (1 : Fin 3)
  have hA2 : A i2 = (fun x : H => (x : G)+2 • r) '' ({0}ᶜ : Set H) := by
    simpa [s,i2] using fiber_one_hole H e 3 (by omega) s hs (2 : Fin 3)
  have ep0 : endpoint (u:G) r ε 0 = (u:G) := endpoint_zero _ _ _
  have ed0 : ε 0 = (v0:G)-(u:G) := by simp [ε,pre]
  have ep1 : endpoint (u:G) r ε 1 = (v0:G)+r := by
    rw [show 1=0+1 from rfl,endpoint_succ,ep0,ed0]; abel
  have ed1 : ε 1 = (v1:G)-(v0:G) := by simp [ε,pre]
  have ep2 : endpoint (u:G) r ε 2 = (v1:G)+2 • r := by
    rw [show 2=1+1 from rfl,endpoint_succ,ep1,ed1]; abel
  have ed2 : ε 2 = (v2:G)-(v1:G) := by simp [ε,pre]
  have paths (j : Fin q) (hj : j.val < pre.length) :
      RainbowPath (A j) (endpoint (u:G) r ε j.val) (endpoint (u:G) r ε j.val+ε j.val) := by
    have hj3 : j.val<3 := by simpa [pre] using hj
    by_cases hj0 : j.val=0
    · have heq : j=i0 := Fin.ext hj0
      subst j
      change RainbowPath (A i0) (endpoint (u:G) r ε 0) (endpoint (u:G) r ε 0+ε 0)
      rw [hA0,ep0,ed0]
      have ht : (u:G)+((v0:G)-(u:G))=(v0:G) := by abel
      rw [ht]
      simpa using path_of_mapped_cycle C H.subtype Subtype.val_injective 0 u v0 hum hv0
        (C.next.apply_symm_apply u)
    by_cases hj1 : j.val=1
    · have heq : j=i1 := Fin.ext hj1
      subst j
      change RainbowPath (A i1) (endpoint (u:G) r ε 1) (endpoint (u:G) r ε 1+ε 1)
      rw [hA1,ep1,ed1]
      have ht : (v0:G)+r+((v1:G)-(v0:G))=(v1:G)+r := by abel
      rw [ht]
      exact path_of_mapped_cycle C H.subtype Subtype.val_injective r v0 v1 hv0 hv1
        (C.next.apply_symm_apply v0)
    · have hj2 : j.val=2 := by omega
      have heq : j=i2 := Fin.ext hj2
      subst j
      change RainbowPath (A i2) (endpoint (u:G) r ε 2) (endpoint (u:G) r ε 2+ε 2)
      rw [hA2,ep2,ed2]
      have ht : (v1:G)+2 • r+((v2:G)-(v1:G))=(v2:G)+2 • r := by abel
      rw [ht]
      exact path_of_mapped_cycle C H.subtype Subtype.val_injective (2 • r) v1 v2 hv1 hv2
        (C.next.apply_symm_apply v1)
  have hc := glue_prefix_paths hodd H hH r (u:G) u.property hgen pre
    (by simp [pre]; omega) (by simp [pre]; omega) A hA paths hfull
  rw [deletedFiber_union] at hc
  have hset : D = {0,r,2 • r} := by
    ext z
    simp [D,s,Set.mem_range,Fin.exists_fin_succ,two_nsmul,eq_comm]
  rwa [hset] at hc

end SunThreeDeletion

