import SunTwoDeletion.EdgeProperty
import SunThreeDeletion.Certificate

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

universe u
variable {G : Type u} [AddCommGroup G]

theorem cycle_restrict_subgroup (H : AddSubgroup G) (A : Set G) (hA : A ⊆ H)
    (h : HasRainbowCycle A) : HasRainbowCycle (H.subtype ⁻¹' A) := by
  classical
  obtain ⟨C⟩ := h
  let p := C.next.subtypePerm (fun _ => C.cyclic.apply_mem_iff)
  let e : A ↪ H := ⟨fun x => ⟨x.val, hA x.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : H => (z : G)) h)⟩
  have hinj : Function.Injective (fun i => e i + e (p i)) := by
    intro i j h
    apply Subtype.ext
    apply C.rainbow i.property j.property
    exact congrArg (fun x : H => (x : G)) h
  have C' := RainbowCycle.ofEmbedding p C.cyclic.subtypePerm e hinj
  have he : Set.range e = H.subtype ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x.val,hx⟩, Subtype.ext rfl⟩
  exact ⟨he ▸ C'⟩

theorem cyclic_extension [Finite G] (hodd : Odd (Nat.card G))
    (H : AddSubgroup G) (hH : 3 ≤ Nat.card H)
    (hq : 3 ≤ Nat.card (G ⧸ H)) [IsAddCyclic (G ⧸ H)]
    (A : Set G) (hA : A ⊆ H) (hne : A.Nonempty)
    (h : HasRainbowCycle A) : HasRainbowCycle ((H : Set G)ᶜ ∪ A) := by
  obtain ⟨C⟩ := h
  obtain ⟨v,hv⟩ := hne
  let u := C.next v
  have hu : u ∈ A := C.cyclic.1.mapsTo hv
  obtain ⟨r,hgen⟩ := quotient_generator_lift H
  obtain ⟨D,_,_⟩ := cyclic_quotient_glue_controlled hodd H hH hq
    (edge_property_odd H (subgroup_odd hodd H)) r hgen A hA C u v hu hv rfl
  exact ⟨D⟩

/-- Extend a nonempty cycle from any nontrivial subgroup. The induction is solely
on the ambient group order, and its recursive call is on a proper subgroup. -/
theorem subgroup_extension (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (H : AddSubgroup G) (hH : 3 ≤ Nat.card H)
    (A : Set G) (hA : A ⊆ H) (hne : A.Nonempty) (h : HasRainbowCycle A) :
    HasRainbowCycle ((H : Set G)ᶜ ∪ A) := by
  suffices aux : ∀ n, ∀ (K : Type u) [AddCommGroup K] [Finite K],
      Nat.card K = n → Odd n →
      ∀ (J : AddSubgroup K), 3 ≤ Nat.card J →
      ∀ (B : Set K), B ⊆ J → B.Nonempty → HasRainbowCycle B →
        HasRainbowCycle ((J : Set K)ᶜ ∪ B) from
    aux (Nat.card G) G rfl hodd H hH A hA hne h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard hodd J hJ B hBJ hBne hB
    classical
    have hoddK : Odd (Nat.card K) := hcard.symm ▸ hodd
    by_cases hJtop : J = ⊤
    · simpa [hJtop] using hB
    letI : Finite (AddSubgroup K) :=
      Finite.of_injective (fun J : AddSubgroup K => (J : Set K)) SetLike.coe_injective
    obtain ⟨L,hL,hJL⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJtop
    let J' : AddSubgroup L := J.addSubgroupOf L
    let B' : Set L := L.subtype ⁻¹' B
    have hJcard : Nat.card J' = Nat.card J :=
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hJL).toEquiv
    have hB'L : B' ⊆ J' := fun x hx => hBJ hx
    have hB'ne : B'.Nonempty := by
      obtain ⟨x,hx⟩ := hBne
      exact ⟨⟨x,hJL (hBJ hx)⟩, hx⟩
    have hB' := cycle_restrict_subgroup L B (fun x hx => hJL (hBJ hx)) hB
    have hlt := proper_subgroup_card_lt L hL.ne_top
    have hinside := ih (Nat.card L) (by omega) L rfl (subgroup_odd hoddK L)
      J' (by omega) B' hB'L hB'ne hB'
    obtain ⟨C⟩ := hinside
    let S : Set K := L.subtype '' ((J' : Set L)ᶜ ∪ B')
    have hS : S ⊆ L := by rintro _ ⟨x,_,rfl⟩; exact x.property
    have hSne : S.Nonempty := by
      obtain ⟨x,hx⟩ := hB'ne
      exact ⟨x, x, Or.inr hx, rfl⟩
    have hcycle : HasRainbowCycle S := ⟨C.map L.subtype Subtype.val_injective⟩
    have hLcard : 3 ≤ Nat.card L := by
      have hle := Nat.card_le_card_of_injective (f := AddSubgroup.inclusion hJL)
        (AddSubgroup.inclusion_injective hJL)
      omega
    have hp := maximal_quotient_prime L hL
    haveI : Fact (Nat.card (K ⧸ L)).Prime := ⟨hp⟩
    haveI : IsAddCyclic (K ⧸ L) := isAddCyclic_of_prime_card rfl
    have hq : 3 ≤ Nat.card (K ⧸ L) := by
      have ho := quotient_odd hoddK L
      have := hp.one_lt
      obtain ⟨q,hq⟩ := ho
      omega
    have hext := cyclic_extension hoddK L hLcard hq S hS hSne hcycle
    have heq : (L : Set K)ᶜ ∪ S = (J : Set K)ᶜ ∪ B := by
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, S, Set.mem_image]
      constructor
      · rintro (hx | ⟨y,hy,rfl⟩)
        · exact Or.inl (fun h => hx (hJL h))
        · rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
      · rintro (hx | hx)
        · by_cases hxL : x ∈ L
          · exact Or.inr ⟨⟨x,hxL⟩, Or.inl hx, rfl⟩
          · exact Or.inl hxL
        · exact Or.inr ⟨⟨x,hJL (hBJ hx)⟩, Or.inr hx, rfl⟩
    rwa [heq] at hext

end SunThreeDeletion

