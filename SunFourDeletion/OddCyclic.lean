import SunFourDeletion.OddSums
import SunThreeDeletion.OneHoleGroup

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

theorem odd_sorted_cycle (M l : ℕ) [NeZero M] (hl : 1≤l)
    (a : Fin (2*l+1) → ℕ) (ha : StrictMono a) (hb : ∀ i, a i<M) :
    HasRainbowCycle (Set.range (fun i => (a i : ZMod M))) := by
  have hcast : Function.Injective (fun i => (a i : ZMod M)) := by
    intro i j he
    apply ha.injective
    have hh := congrArg ZMod.val he
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb i),Nat.mod_eq_of_lt (hb j)] using hh
  let v : Fin (2*l+1) ↪ ZMod M :=
    ⟨fun i => a (zigIndex l i), hcast.comp (zigIndex_injective l)⟩
  have hc : Function.Injective (fun i => v i + v (finRotate (2*l+1) i)) := by
    intro i j he
    apply colorIndex_injective l
    apply sortedSum_cast_injective M l a ha hb
    change (a (zigIndex l i) : ZMod M) + a (zigIndex l (finRotate (2*l+1) i)) =
      (a (zigIndex l j) : ZMod M) + a (zigIndex l (finRotate (2*l+1) j)) at he
    simpa only [← Nat.cast_add,zig_sum l hl a] using he
  have hh := RainbowCycle.ofEmbedding (finRotate (2*l+1))
    (finRotate_isCycleOn (by omega)) v hc
  have hs : Set.range v = Set.range (fun i => (a i : ZMod M)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨zigIndex l i,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := Finite.surjective_of_injective (zigIndex_injective l) i
      exact ⟨j,rfl⟩
  exact ⟨hs ▸ hh⟩

/-- Every odd subset of a finite cyclic group, even an even-order ambient group. -/
theorem odd_zmod_subset (M : ℕ) [NeZero M] (s : Finset (ZMod M))
    (hodd : Odd s.card) (hsize : 3≤s.card) : HasRainbowCycle (s : Set (ZMod M)) := by
  classical
  obtain ⟨l,hl⟩ := hodd
  have hs : s.card=2*l+1 := by omega
  have hlpos : 1≤l := by omega
  let t : Finset ℕ := s.image ZMod.val
  have ht : t.card=2*l+1 := by
    rw [Finset.card_image_of_injective s (ZMod.val_injective M)]
    exact hs
  let a := t.orderEmbOfFin ht
  have hb (i) : a i<M := by
    have hm := Finset.orderEmbOfFin_mem t ht i
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hm
    change z.val=a i at he
    rw [← he]
    exact ZMod.val_lt z
  have hc := odd_sorted_cycle M l hlpos a a.strictMono hb
  have he : Set.range (fun i => (a i : ZMod M)) = (s : Set (ZMod M)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      have hm := Finset.orderEmbOfFin_mem t ht i
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hm
      change z.val=a i at he
      simpa only [← he,ZMod.natCast_zmod_val,Finset.mem_coe] using hz
    · intro hx
      have hx' : x.val ∈ t := Finset.mem_image.mpr ⟨x,hx,rfl⟩
      have hr := Finset.range_orderEmbOfFin t ht
      obtain ⟨i,hi⟩ := hr.symm.subset hx'
      refine ⟨i,?_⟩
      change (a i : ZMod M)=x
      change a i=x.val at hi
      rw [hi,ZMod.natCast_zmod_val]
  exact he ▸ hc

theorem odd_cyclic_subset (G : Type*) [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (s : Finset G) (hodd : Odd s.card) (hsize : 3≤s.card) :
    HasRainbowCycle (s : Set G) := by
  classical
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let e : ZMod (Nat.card G) ≃+ G := zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic G)
  let t := s.map e.symm.toEmbedding
  have ht : t.card=s.card := Finset.card_map _
  obtain ⟨C⟩ := odd_zmod_subset (Nat.card G) t (ht.symm ▸ hodd) (ht.symm ▸ hsize)
  have hc := C.map e.toAddMonoidHom e.injective
  have he : e '' (t : Set (ZMod (Nat.card G))) = (s : Set G) := by
    ext x
    simp only [Set.mem_image,Finset.mem_coe,t,Finset.mem_map]
    constructor
    · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x,⟨x,hx,rfl⟩,e.apply_symm_apply x⟩
  exact ⟨he ▸ hc⟩

end SunFourDeletion
