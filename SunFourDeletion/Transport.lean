import SunThreeDeletion.SubgroupExtension

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem complement_finset_nonempty (D : Finset G) (h : D.card < Nat.card G) :
    ((D : Set G)ᶜ).Nonempty := by
  classical
  letI := Fintype.ofFinite G
  have hd : (Dᶜ : Finset G).card>0 := by
    rw [Finset.card_compl]
    rw [Nat.card_eq_fintype_card] at h
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hd
  exact ⟨x,by simpa using hx⟩

theorem lift_finset_cycle (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3≤Nat.card H) (D : Finset H) (hD : D.card<Nat.card H)
    (hc : HasRainbowCycle ((D : Set H)ᶜ)) :
    HasRainbowCycle ((H.subtype '' (D : Set H))ᶜ) := by
  obtain ⟨C⟩ := hc
  let A : Set G := H.subtype '' ((D : Set H)ᶜ)
  have hA : A ⊆ H := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have hne : A.Nonempty := (complement_finset_nonempty D hD).image H.subtype
  have hh := subgroup_extension G hodd H hH A hA hne
    ⟨C.map H.subtype Subtype.val_injective⟩
  have he : (H : Set G)ᶜ ∪ A = (H.subtype '' (D : Set H))ᶜ := by
    ext x
    constructor
    · rintro (hx | ⟨y,hy,rfl⟩) ⟨z,hz,he⟩
      · exact hx (he ▸ z.property)
      · exact hy (Subtype.val_injective he ▸ hz)
    · intro hx
      by_cases hm : x∈H
      · right
        refine ⟨⟨x,hm⟩,?_,rfl⟩
        intro hd
        exact hx ⟨⟨x,hm⟩,hd,rfl⟩
      · exact Or.inl hm
  rwa [he] at hh

theorem affine_cycle {K : Type*} [AddCommGroup K]
    (e : K ≃+ G) (t : G) (A : Set K) (h : HasRainbowCycle A) :
    HasRainbowCycle ((fun x => e x+t) '' A) := by
  obtain ⟨C⟩ := h
  have hh := (C.map e.toAddMonoidHom e.injective).translate t
  have he : (fun x : G => x+t) '' (e '' A) = (fun x => e x+t) '' A := Set.image_image _ _ _
  exact ⟨he ▸ hh⟩

theorem translate_complement (A : Set G) (t : G) :
    (fun x => x+t) '' Aᶜ = ((fun x => x+t) '' A)ᶜ :=
  Set.image_compl_eq (Equiv.addRight t).bijective

theorem translate_finset_cycle (D : Finset G) (t : G)
    (h : HasRainbowCycle ((D : Set G)ᶜ)) :
    HasRainbowCycle ((D.map (Equiv.addRight t).toEmbedding : Set G)ᶜ) := by
  obtain ⟨C⟩ := h
  have hh := C.translate t
  rw [translate_complement] at hh
  have he : (fun x : G => x+t) '' (D : Set G) =
      (D.map (Equiv.addRight t).toEmbedding : Set G) := by
    ext x
    simp only [Set.mem_image,Finset.mem_coe,Finset.mem_map]
    rfl
  exact ⟨he ▸ hh⟩

theorem lift_shifted_cycle (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (hH : 3≤Nat.card H) (D : Finset H) (hD : D.card<Nat.card H) (t : G)
    (hc : HasRainbowCycle ((D : Set H)ᶜ)) :
    HasRainbowCycle (((fun x : H => (x : G)+t) '' (D : Set H))ᶜ) := by
  obtain ⟨C⟩ := lift_finset_cycle hodd H hH D hD hc
  have hh := C.translate t
  rw [translate_complement,Set.image_image] at hh
  exact ⟨hh⟩

theorem translate_filter_card {K : Type*} [AddCommGroup K] [DecidableEq K]
    (f : G →+ K) (D : Finset G) (t : G) (y : K) :
    ((D.map (Equiv.addRight t).toEmbedding).filter (fun x => f x=y)).card =
      (D.filter (fun x => f x=y-f t)).card := by
  classical
  rw [Finset.filter_map,Finset.card_map]
  congr 1
  ext x
  simp [Function.comp_def,eq_sub_iff_add_eq]

end SunFourDeletion
