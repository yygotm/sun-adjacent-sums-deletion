import SunFourDeletion.NormalizeFiber

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

theorem thin_hom_cycle {G : Type*} [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (p : ℕ) [Fact p.Prime] (hp : 5≤p)
    (f : G →+ ZMod p) (hf : Function.Surjective f) (hH : 5≤Nat.card f.ker)
    (D : Finset G) (hD : D.card=4)
    (hthin : ∀ y : ZMod p, (D.filter (fun x => f x=y)).card≤2) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let H := f.ker
  have hH' : 5≤Nat.card H := hH
  letI := Fintype.ofFinite H
  let Q := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  have hq : Nat.card (G ⧸ H)=p := by
    have hh := Nat.card_congr Q.toEquiv
    simpa using hh
  haveI : IsAddCyclic (G ⧸ H) := isAddCyclic_of_prime_card hq
  have hsmall : (D.image f).card<Nat.card (ZMod p) := by
    have hh := Finset.card_image_le (s := D) (f := f)
    simp only [Nat.card_zmod]
    omega
  obtain ⟨v,hv⟩ := complement_finset_nonempty (D.image f) hsmall
  have hmiss : ∀ d∈D, (QuotientAddGroup.mk d : G ⧸ H) ≠ Q.symm v := by
    intro d hd he
    have hh := congrArg Q he
    rw [Q.apply_symm_apply] at hh
    exact hv (Finset.mem_image.mpr ⟨d,hd,hh⟩)
  obtain ⟨r,hgen⟩ := quotient_generator_lift H
  obtain ⟨s,hs⟩ := align_full_fiber H r D (Q.symm v) hmiss
  let E := D.map (Equiv.addRight (-s)).toEmbedding
  have hE : E.card=4 := by simpa [E] using hD
  have hEfilter (y : ZMod p) : (E.filter (fun x => f x=y)).card≤2 := by
    rw [translate_filter_card]
    exact hthin _
  let e := cosetCoordinates hodd H r hgen
  let F := productHoles e E
  have hF (i) : (F i).card≤2 := by
    have hsub : (F i).map (fiberEmbedding e i) ⊆ E.filter (fun x => f x=f (i.val • r)) := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
      refine Finset.mem_filter.mpr ⟨(mem_productHoles e E i u).mp hu,?_⟩
      change f ((u : G)+i.val • r)=_
      rw [map_add]
      have hz : f (u : G)=0 := u.property
      rw [hz,zero_add]
    have hh := (Finset.card_le_card hsub).trans (hEfilter _)
    simpa only [Finset.card_map] using hh
  have hc : HasRainbowCycle ((E : Set G)ᶜ) := by
    apply glue_deleted_fibers hodd H r hgen (by omega) E hs (by omega)
    intro i
    have hi := hF i
    change (F i).card≤3 ∧ 3≤Nat.card H-(F i).card
    omega
  exact undo_translation_cycle D s hc

end SunFourDeletion
