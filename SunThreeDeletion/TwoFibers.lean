import SunThreeDeletion.PrefixGlue
import SunThreeDeletion.Orient
import SunThreeDeletion.MappedPaths
import SunThreeDeletion.Fibers
import SunTwoDeletion.Main

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Two holes in H and one in a generating coset. The quotient may have order
three and H need not be a direct factor. -/
theorem two_punctured_fibers (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 5 ≤ Nat.card H) (hq : 3 ≤ Nat.card (G ⧸ H)) (r : G)
    (hgen : ∀ z : G ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (d : H) (hd : d ≠ 0)
    (C1 : RainbowCycle ({0}ᶜ : Set H)) :
    HasRainbowCycle ({0,(d : G),r}ᶜ : Set G) := by
  classical
  letI := Fintype.ofFinite H
  let q := Nat.card (G ⧸ H)
  let R : G ⧸ H := QuotientAddGroup.mk r
  let e := natOrbit (quotient_odd hodd H) R hgen
  let i0 : Fin q := ⟨0,by omega⟩
  let i1 : Fin q := ⟨1,by omega⟩
  have he0 : e i0 = 0 := by rw [natOrbit_apply]; simp [i0]
  have he1 : e i1 = R := by rw [natOrbit_apply]; simp [i1]
  have hR : R ≠ 0 := by
    intro heq
    have h := e.injective (he1.trans (heq.trans he0.symm))
    have hv := congrArg Fin.val h
    change 1 = 0 at hv
    omega
  have hrH : r ∉ H := fun h => hR ((QuotientAddGroup.eq_zero_iff r).mpr h)
  have hr0 : r ≠ 0 := fun h => hrH (h ▸ H.zero_mem)
  have hdr : (d : G) ≠ r := fun h => hrH (h ▸ d.property)
  have hoH := subgroup_odd hodd H
  obtain ⟨C0,_⟩ := sun_two_deletion_exact H hoH (by omega) 0 d hd.symm
  let v : H := d+d
  have hv0 : v ≠ 0 := by
    intro h
    apply hd
    apply double_injective hoH
    simpa [v] using h
  have hvd : v ≠ d := by simpa [v] using hd
  have hv : v ∈ ({0,d}ᶜ : Set H) := by simpa using And.intro hv0 hvd
  let u : H := C0.next v
  have hu : u ∈ ({0,d}ᶜ : Set H) := C0.cyclic.1.mapsTo hv
  let qr : H := ⟨q • r, quotient_card_nsmul_mem H r⟩
  have hc1 : 3 ≤ Nat.card ({0}ᶜ : Set H) := by
    have hc : Nat.card ({0}ᶜ : Set H) = Nat.card H-1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      simp [Nat.card_eq_fintype_card]
    omega
  obtain ⟨D1,w,hw,hclose,hwne⟩ := predecessor_avoiding C1 hc1 v (by simpa using hv0) (u-qr)
  let pre : List H := [v-u,w-v]
  let ε : ℕ → G := fun i => (pre.getD i 0 : G)
  have hsum : (pre.sum : G) = (w : G)-(u : G) := by
    simp [pre]
  have hres : pre.length+1=q → -(q • r) ≠ (pre.sum : G) := by
    intro _ h
    apply hwne
    apply Subtype.ext
    rw [hsum] at h
    change (w : G) = (u : G)-q • r
    calc
      (w : G) = ((w : G)-(u : G))+(u : G) := by abel
      _ = -(q • r)+(u : G) := by rw [← h]
      _ = (u : G)-q • r := by abel
  let D : Set G := {0,(d : G),r}
  let A := deletedFiber H e D
  have hA : ∀ j z, z ∈ A j →
      (QuotientAddGroup.mk z : G ⧸ H) = j.val • (QuotientAddGroup.mk r : G ⧸ H) := by
    intro j z hz
    exact hz.1.trans (natOrbit_apply (quotient_odd hodd H) R hgen j)
  have hD : ∀ z ∈ D, ∃ i : Fin q, i.val<2 ∧ (QuotientAddGroup.mk z : G ⧸ H) = e i := by
    intro z hz
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨i0,by change 0<2; decide,by simpa only [he0] using (QuotientAddGroup.eq_zero_iff (0:G)).mpr H.zero_mem⟩
    · exact ⟨i0,by change 0<2; decide,by rw [he0]; exact (QuotientAddGroup.eq_zero_iff _).mpr d.property⟩
    · exact ⟨i1,by change 1<2; decide,he1.symm⟩
  have hfull (j : Fin q) (hj : pre.length ≤ j.val) :
      A j = {z | (QuotientAddGroup.mk z : G ⧸ H) = j.val • R} := by
    change deletedFiber H e D j = _
    rw [deletedFiber_full H e D 2 hD j (by simpa [pre] using hj)]
    rw [natOrbit_apply]
  have hA0 : A i0 = (fun x : H => (x : G)+0) '' ({0,d}ᶜ : Set H) := by
    change {z | (QuotientAddGroup.mk z : G ⧸ H) = e i0} \ D = _
    rw [he0]
    have hz : (0 : G ⧸ H) = QuotientAddGroup.mk (0 : G) := rfl
    rw [hz, fiber_as_image]
    congr 1
    ext x
    have hxr : (x : G) ≠ r := fun h => hrH (h ▸ x.property)
    have hx0 : (x : G) = 0 ↔ x = 0 := ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    have hxd : (x : G) = (d : G) ↔ x = d := Subtype.val_injective.eq_iff
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, D, add_zero,
      Set.mem_insert_iff, Set.mem_singleton_iff, hxr, or_false, hx0, hxd]
  have hA1 : A i1 = (fun x : H => (x : G)+r) '' ({0}ᶜ : Set H) := by
    change {z | (QuotientAddGroup.mk z : G ⧸ H) = e i1} \ D = _
    rw [he1, fiber_as_image]
    congr 1
    ext x
    have hx0 : (x : G)+r ≠ 0 := by
      intro h
      apply hrH
      have hr : r = -(x : G) := by exact eq_neg_of_add_eq_zero_right h
      rw [hr]
      exact H.neg_mem x.property
    have hxd : (x : G)+r ≠ (d : G) := by
      intro h
      apply hrH
      have hr : r = (d : G)-(x : G) := by exact eq_sub_of_add_eq' h
      rw [hr]
      exact H.sub_mem d.property x.property
    have hxeq : (x : G) = 0 ↔ x = 0 := ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, D, Set.mem_insert_iff,
      Set.mem_singleton_iff, hx0, hxd, false_or, add_eq_right, hxeq]
  have ep0 : endpoint (u : G) r ε 0 = (u : G) := endpoint_zero _ _ _
  have ed0 : ε 0 = (v : G)-(u : G) := by simp [ε,pre]
  have ep1 : endpoint (u : G) r ε 1 = (v : G)+r := by
    rw [show 1=0+1 from rfl, endpoint_succ, ep0, ed0]
    abel
  have ed1 : ε 1 = (w : G)-(v : G) := by simp [ε,pre]
  have paths (j : Fin q) (hj : j.val < pre.length) :
      RainbowPath (A j) (endpoint (u : G) r ε j.val)
        (endpoint (u : G) r ε j.val+ε j.val) := by
    have hj' : j.val=0 ∨ j.val=1 := by simp only [pre,List.length_cons,List.length_nil] at hj; omega
    by_cases hj0 : j.val=0
    · have heq : j=i0 := Fin.ext hj0
      subst j
      change RainbowPath (A i0) (endpoint (u:G) r ε 0) (endpoint (u:G) r ε 0+ε 0)
      rw [hA0, ep0, ed0]
      have ht : (u:G)+((v:G)-(u:G)) = (v:G) := by abel
      rw [ht]
      simpa using path_of_mapped_cycle C0 H.subtype Subtype.val_injective 0 u v hu hv rfl
    · have hj1 : j.val=1 := by omega
      have heq : j=i1 := Fin.ext hj1
      subst j
      change RainbowPath (A i1) (endpoint (u:G) r ε 1) (endpoint (u:G) r ε 1+ε 1)
      rw [hA1, ep1, ed1]
      have ht : (v:G)+r+((w:G)-(v:G)) = (w:G)+r := by abel
      rw [ht]
      exact path_of_mapped_cycle D1 H.subtype Subtype.val_injective r v w (by simpa using hv0) hw hclose
  have hcycle := glue_prefix_paths hodd H (by omega) r (u:G) u.property hgen pre
    (by simpa [pre] using hq) hres A hA paths hfull
  rw [deletedFiber_union] at hcycle
  exact hcycle

end SunThreeDeletion

