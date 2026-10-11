import SunFourDeletion.EndpointChoice
import SunFourDeletion.RelativeGlue
import SunTwoDeletion.EdgeProperty

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Lemma A: a full last fiber absorbs the residual endpoint, including q*r. -/
theorem glue_one_full_fiber (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    (r : G)
    (hgen : ∀ x : G ⧸ H, x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk r))
    (hq : 3 ≤ Nat.card (G ⧸ H))
    (D : Fin (Nat.card (G ⧸ H)) → Finset H)
    (hlast : D ⟨Nat.card (G ⧸ H)-1,by omega⟩ = ∅)
    (hcycles : ∀ i, HasRainbowCycle ((D i : Set H)ᶜ))
    (hsize : ∀ i, 3 ≤ Nat.card {x : H // x ∉ D i})
    (hsmall : (∑ i : Fin (Nat.card (G ⧸ H)-1),
      (D ⟨i.val,by have := i.isLt; omega⟩).card) < Nat.card H) :
    HasRainbowCycle (⋃ i : Fin (Nat.card (G ⧸ H)),
      (fun x : H => (x : G)+i.val • r) '' ((D i : Set H)ᶜ)) := by
  classical
  letI := Fintype.ofFinite H
  let q := Nat.card (G ⧸ H)
  let incl : Fin (q-1) → Fin q := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let E : Fin (q-1) → Finset H := fun i => D (incl i)
  let C : ∀ i, RainbowCycle ((E i : Set H)ᶜ) := fun i => Classical.choice (hcycles (incl i))
  let c : H := ⟨q • r,quotient_card_nsmul_mem H r⟩
  obtain ⟨z,hw,hpaths⟩ := cycle_chain_endpoints (q-1) (by omega) E C
    (fun i => hsize (incl i)) (by simpa only [Nat.card_eq_fintype_card] using hsmall) c
  let z' : ℕ → H := fun n => if n=q then z 0-c else z n
  have hz (n : ℕ) (hn : n<q) : z' n=z n := if_neg (Nat.ne_of_lt hn)
  have hzq : z' q=z 0-c := by simp [z']
  have hclose : (z' q : G)+q • r=(z' 0 : G) := by
    rw [hzq,hz 0 (by omega)]
    change (z 0 : G)-q • r+q • r=(z 0 : G)
    abel
  have hP (i : Fin q) : ∃ P : RainbowCycle ((D i : Set H)ᶜ),
      z' i.val ∈ (D i : Set H)ᶜ ∧ z' (i.val+1) ∈ (D i : Set H)ᶜ ∧
      P.next (z' (i.val+1))=z' i.val := by
    by_cases hi : i.val<q-1
    · obtain ⟨P,hx,hy,he⟩ := hpaths ⟨i.val,hi⟩
      change ∃ P : RainbowCycle ((D i : Set H)ᶜ), _
      refine ⟨P,?_,?_,?_⟩
      · rw [hz i.val i.isLt]; exact hx
      · rw [hz (i.val+1) (by omega)]; exact hy
      · rw [hz i.val i.isLt,hz (i.val+1) (by omega)]; exact he
    · have hiv : i.val=q-1 := by have := i.isLt; omega
      have hii : i=⟨q-1,by omega⟩ := Fin.ext hiv
      have hDi : D i=∅ := hii ▸ hlast
      obtain ⟨P,hP⟩ := edge_property_odd H (subgroup_odd hodd H) (z 0-c) (z (q-1)) hw.symm
      have hs : (D i : Set H)ᶜ = Set.univ := by rw [hDi]; simp
      let P' : RainbowCycle ((D i : Set H)ᶜ) :=
        ⟨P.next,hs.symm ▸ P.cyclic,hs.symm ▸ P.rainbow⟩
      refine ⟨P',by rw [hs]; trivial,by rw [hs]; trivial,?_⟩
      change P.next (z' (i.val+1))=z' i.val
      rw [hz i.val i.isLt,hiv]
      have he : q-1+1=q := by omega
      rw [he,hzq]
      exact hP
  exact glue_relative_cycles hodd H r hgen (fun i => (D i : Set H)ᶜ)
    (fun i => Classical.choose (hP i)) z' hclose
    (fun i => (Classical.choose_spec (hP i)).1)
    (fun i => (Classical.choose_spec (hP i)).2.1)
    (fun i => (Classical.choose_spec (hP i)).2.2)

end SunFourDeletion
