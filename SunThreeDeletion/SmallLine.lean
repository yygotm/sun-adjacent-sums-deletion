import SunThreeDeletion.SmallStructure
import SunThreeDeletion.SmallCases
import SunThreeDeletion.AffineTemplates

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_line_cycle (n p k : ℕ)
    (hn : (n=9 ∧ p=3 ∧ k=3) ∨ (n=15 ∧ p=5 ∧ k=3) ∨ (n=25 ∧ p=5 ∧ k=5))
    (d : ZMod n) (hd : d ≠ 0) (hp : p • d=0) :
    HasRainbowCycle ({0,d,2 • d}ᶜ : Set (ZMod n)) := by
  have hb : HasRainbowCycle ({0,(k : ZMod n),2 • (k : ZMod n)}ᶜ : Set (ZMod n)) := by
    rcases hn with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · simpa only [Nat.cast_ofNat,two_nsmul,show (3 : ZMod 9)+3=6 by decide] using base_C9_line
    · simpa only [Nat.cast_ofNat,two_nsmul,show (3 : ZMod 15)+3=6 by decide] using base_C15_line
    · simpa only [Nat.cast_ofNat,two_nsmul,show (5 : ZMod 25)+5=10 by decide] using base_C25_line
  have hu : ∃ u : Fin n, u.val.Coprime n ∧ (k : ZMod n)*u.val=d := by
    rcases hn with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · have h : ∀ d : ZMod 9, d≠0 → 3 • d=0 →
          ∃ u : Fin 9, u.val.Coprime 9 ∧ (3 : ZMod 9)*u.val=d := by decide
      exact h d hd hp
    · have h : ∀ d : ZMod 15, d≠0 → 5 • d=0 →
          ∃ u : Fin 15, u.val.Coprime 15 ∧ (3 : ZMod 15)*u.val=d := by decide
      exact h d hd hp
    · have h : ∀ d : ZMod 25, d≠0 → 5 • d=0 →
          ∃ u : Fin 25, u.val.Coprime 25 ∧ (5 : ZMod 25)*u.val=d := by decide
      exact h d hd hp
  obtain ⟨u,huc,hu⟩ := hu
  let v := ZMod.unitOfCoprime u.val huc
  have hv : ((v : (ZMod n)ˣ) : ZMod n)=u.val := rfl
  have hh := affine_three_cycle (AddAut.mulRight v) 0 0 (k : ZMod n) (2 • (k : ZMod n)) hb
  have h2 : (2 • (k : ZMod n))*(u.val : ZMod n)=2 • d := by simp only [two_nsmul,add_mul,hu]
  simpa only [AddAut.mulRight_apply,hv,zero_mul,add_zero,hu,h2] using hh

theorem small_cyclic_line {G : Type*} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (p k : ℕ) (hn : (Nat.card G=9 ∧ p=3 ∧ k=3) ∨
      (Nat.card G=15 ∧ p=5 ∧ k=3) ∨ (Nat.card G=25 ∧ p=5 ∧ k=5))
    (d : G) (hd : d≠0) (hp : p • d=0) :
    HasRainbowCycle ({0,d,2 • d}ᶜ : Set G) := by
  let e := zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic G)
  have hd' : e.symm d ≠ 0 := by intro h; apply hd; simpa using congrArg e h
  have hp' : p • e.symm d=0 := by rw [← map_nsmul,hp,map_zero]
  have hh := finite_line_cycle (Nat.card G) p k hn (e.symm d) hd' hp'
  have hh' := affine_three_cycle e 0 0 (e.symm d) (2 • e.symm d) hh
  simpa only [map_zero,zero_add,add_zero,map_nsmul,AddEquiv.apply_symm_apply] using hh'

theorem small_prime_triple_ap {G : Type*} [AddCommGroup G] [Finite G]
    (hc : Nat.card G=3 ∨ Nat.card G=5) (a b c : G)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    ∃ s d : G, d≠0 ∧ ({a,b,c} : Set G)={s,s+d,s+2 • d} := by
  have hall : ∀ x y z : ZMod (Nat.card G), x≠y → x≠z → y≠z →
      ∃ s d : ZMod (Nat.card G), d≠0 ∧
        ({x,y,z} : Finset (ZMod (Nat.card G)))={s,s+d,s+2 • d} := by
    rcases hc with h | h
    · rw [h]; decide
    · rw [h]; decide
  haveI : Fact (Nat.card G).Prime := ⟨by rcases hc with h | h <;> rw [h] <;> decide⟩
  haveI : IsAddCyclic G := isAddCyclic_of_prime_card rfl
  let e := zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic G)
  obtain ⟨s,d,hd,he⟩ := hall (e.symm a) (e.symm b) (e.symm c)
    (fun h => hab (e.symm.injective h)) (fun h => hac (e.symm.injective h))
    (fun h => hbc (e.symm.injective h))
  refine ⟨e s,e d,fun h => hd (e.injective (by simpa using h)),?_⟩
  have he' : ({e.symm a,e.symm b,e.symm c} : Set (ZMod (Nat.card G)))={s,s+d,s+2 • d} := by
    have hh := congrArg (fun F : Finset (ZMod (Nat.card G)) => (F : Set (ZMod (Nat.card G)))) he
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hh
  have hh := congrArg (fun A : Set (ZMod (Nat.card G)) => e '' A) he'
  simpa only [Set.image_insert_eq,Set.image_singleton,AddEquiv.apply_symm_apply,
    map_add,map_nsmul] using hh

end SunThreeDeletion

