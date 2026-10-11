import SunTwoDeletion.Rows
import SunTwoDeletion.Ordering
import SunTwoDeletion.EdgeProperty

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

namespace QuotientRows
variable {G : Type*} [AddCommGroup G] [Finite G]
variable (H : AddSubgroup G) {n : ℕ} (hn : 0 < n)
    (v : Fin n ↪ G ⧸ H) (r : Fin n → G)
    (hr : ∀ j, (QuotientAddGroup.mk (r j) : G ⧸ H) = v j)

def value (a : Σ _ : H, Fin n) : G := a.1+r a.2

include hr in
theorem value_quotient (a : Σ _ : H, Fin n) :
    (QuotientAddGroup.mk (value H r a) : G ⧸ H) = v a.2 := by
  change (QuotientAddGroup.mk' H) ((a.1 : G)+r a.2) = _
  rw [map_add]
  have hz : (QuotientAddGroup.mk' H) (a.1 : G) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr a.1.property
  rw [hz,zero_add]
  exact hr a.2

include hr in
theorem value_injective : Function.Injective (value H r) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have hij : i=j := by
    apply v.injective
    have hh := congrArg (fun z => (QuotientAddGroup.mk z : G ⧸ H)) h
    simpa only [value_quotient H v r hr] using hh
  subst j
  have hab : a=b := Subtype.ext (add_right_cancel h)
  subst b
  rfl

def vertex : (Σ _ : H, Fin n) ↪ G := ⟨value H r,value_injective H v r hr⟩

theorem vertex_range :
    Set.range (vertex H v r hr) = (QuotientAddGroup.mk : G → G ⧸ H) ⁻¹' Set.range v := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a.2,(value_quotient H v r hr a).symm⟩
  · rintro ⟨j,hj⟩
    have hm : z-r j ∈ H := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' H) (z-r j) = 0
      rw [map_sub]
      change (QuotientAddGroup.mk z : G ⧸ H)-QuotientAddGroup.mk (r j)=0
      rw [hr j,← hj,sub_self]
    exact ⟨⟨⟨z-r j,hm⟩,j⟩,sub_add_cancel z (r j)⟩

variable (C : RainbowCycle (Set.univ : Set H))

noncomputable def next : Equiv.Perm (Σ _ : H, Fin n) :=
  blockPerm (fun _ => n) (fun _ => hn) C.next

noncomputable def color (a : Σ _ : H, Fin n) : G :=
  value H r a+value H r (next H hn C a)

include hr in
theorem color_quotient (a : Σ _ : H, Fin n) :
    (QuotientAddGroup.mk (color H hn r C a) : G ⧸ H) =
      v a.2 + v (cyclicSuccessor hn a.2) := by
  obtain ⟨h,j⟩ := a
  change (QuotientAddGroup.mk' H) (value H r ⟨h,j⟩+value H r (next H hn C ⟨h,j⟩)) = _
  rw [map_add]
  change (QuotientAddGroup.mk (value H r ⟨h,j⟩) : G ⧸ H) +
    QuotientAddGroup.mk (value H r (next H hn C ⟨h,j⟩)) = _
  rw [value_quotient H v r hr,value_quotient H v r hr]
  by_cases hj : j.val+1<n
  · simp only [next,blockPerm_apply,blockNext,cyclicSuccessor,dif_pos hj]
  · simp only [next,blockPerm_apply,blockNext,cyclicSuccessor,dif_neg hj]

include hr in
theorem color_injective (hodd : Odd (Nat.card G))
    (hc : Function.Injective (fun i => v i+v (cyclicSuccessor hn i))) :
    Function.Injective (color H hn r C) := by
  rintro ⟨h,j⟩ ⟨k,l⟩ heq
  have hjl : j=l := by
    apply hc
    have hh := congrArg (fun z => (QuotientAddGroup.mk z : G ⧸ H)) heq
    simpa only [color_quotient H hn v r hr C] using hh
  subst l
  have hhk : h=k := by
    by_cases hj : j.val+1<n
    · have hnext (a : H) : next H hn C ⟨a,j⟩ = ⟨a,⟨j.val+1,hj⟩⟩ := by
        simp only [next,blockPerm_apply,blockNext,dif_pos hj]
      change value H r ⟨h,j⟩+value H r (next H hn C ⟨h,j⟩) =
        value H r ⟨k,j⟩+value H r (next H hn C ⟨k,j⟩) at heq
      rw [hnext h,hnext k] at heq
      apply Subtype.ext
      apply double_injective hodd
      change (h:G)+(h:G)=(k:G)+(k:G)
      apply add_right_cancel (b := r j+r ⟨j.val+1,hj⟩)
      calc
        _ = ((h:G)+r j)+((h:G)+r ⟨j.val+1,hj⟩) := by abel
        _ = ((k:G)+r j)+((k:G)+r ⟨j.val+1,hj⟩) := heq
        _ = _ := by abel
    · have hnext (a : H) : next H hn C ⟨a,j⟩ = ⟨C.next a,⟨0,hn⟩⟩ := by
        simp only [next,blockPerm_apply,blockNext,dif_neg hj]
      change value H r ⟨h,j⟩+value H r (next H hn C ⟨h,j⟩) =
        value H r ⟨k,j⟩+value H r (next H hn C ⟨k,j⟩) at heq
      rw [hnext h,hnext k] at heq
      apply C.rainbow trivial trivial
      apply Subtype.ext
      change (h:G)+(C.next h:G)=(k:G)+(C.next k:G)
      apply add_right_cancel (b := r j+r ⟨0,hn⟩)
      calc
        _ = ((h:G)+r j)+((C.next h:G)+r ⟨0,hn⟩) := by abel
        _ = ((k:G)+r j)+((C.next k:G)+r ⟨0,hn⟩) := heq
        _ = _ := by abel
  subst k
  rfl

include r hr C in
theorem cycle (hodd : Odd (Nat.card G))
    (hc : Function.Injective (fun i => v i+v (cyclicSuccessor hn i))) :
    HasRainbowCycle ((QuotientAddGroup.mk : G → G ⧸ H) ⁻¹' Set.range v) := by
  let c := RainbowCycle.ofEmbedding (next H hn C)
    (blockPerm_cyclic _ _ C.next C.cyclic) (vertex H v r hr)
    (color_injective H hn v r hr C hodd hc)
  exact ⟨vertex_range H v r hr ▸ c⟩
end QuotientRows

theorem quotient_preimage_cycle {G : Type*} [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (A : Set (G ⧸ H)) (hne : A.Nonempty) (h : HasRainbowCycle A) :
    HasRainbowCycle ((QuotientAddGroup.mk : G → G ⧸ H) ⁻¹' A) := by
  classical
  obtain ⟨C⟩ := h
  let s := A.toFinite.toFinset
  have hs : (s : Set (G ⧸ H)) = A := Set.Finite.coe_toFinset _
  let C' : RainbowCycle (s : Set (G ⧸ H)) := ⟨C.next,hs.symm ▸ C.cyclic,hs.symm ▸ C.rainbow⟩
  obtain ⟨u,hu⟩ := hne
  obtain ⟨hn,v,hv,hc,_⟩ := cycle_as_ordering s C' u (hs.symm.subset hu)
  let r : Fin s.card → G := fun j => Classical.choose (QuotientAddGroup.mk_surjective (v j))
  have hr (j) : (QuotientAddGroup.mk (r j) : G ⧸ H) = v j :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (v j))
  obtain ⟨CH⟩ := full_cycle_of_edge_property (edge_property_odd H (subgroup_odd hodd H))
  have hh := QuotientRows.cycle H hn v r hr CH hodd hc
  rwa [hv,hs] at hh

end SunThreeDeletion

