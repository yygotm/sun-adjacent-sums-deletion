import SunTwoDeletion.Basic

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- A rainbow cycle missing two vertices cannot miss any colors beyond two
distinct forbidden colors. This is a finite pigeonhole argument. -/
theorem exact_colors_of_two_forbidden (a b p q : G) (hab : a ≠ b) (hpq : p ≠ q)
    (c : RainbowCycle ({a, b}ᶜ : Set G)) (hp : p ∉ c.colors) (hq : q ∉ c.colors) :
    c.colors = ({p, q}ᶜ : Set G) := by
  classical
  let f : G → G := fun x => if x = a then p else if x = b then q else x + c.next x
  have hmem {x : G} (ha : x ≠ a) (hb : x ≠ b) : x ∈ ({a, b}ᶜ : Set G) := by
    simpa using And.intro ha hb
  have hcp {x : G} (ha : x ≠ a) (hb : x ≠ b) : x + c.next x ≠ p := by
    intro h
    exact hp ⟨x, hmem ha hb, h⟩
  have hcq {x : G} (ha : x ≠ a) (hb : x ≠ b) : x + c.next x ≠ q := by
    intro h
    exact hq ⟨x, hmem ha hb, h⟩
  have hinj : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    split_ifs at h with hxa hya hyb hxb hya hyb hya hyb
    · exact hxa.trans hya.symm
    · exact (hpq h).elim
    · exact (hcp hya hyb h.symm).elim
    · exact (hpq h.symm).elim
    · exact hxb.trans hyb.symm
    · exact (hcq hya hyb h.symm).elim
    · exact (hcp hxa hxb h).elim
    · exact (hcq hxa hxb h).elim
    · exact c.rainbow (hmem hxa hxb) (hmem hya hyb) h
  have hsurj := Finite.surjective_of_injective hinj
  ext z
  constructor
  · intro hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hp (h ▸ hz), fun h => hq (h ▸ hz)⟩
  · intro hz
    have hzp : z ≠ p := fun h => hz (by simp [h])
    have hzq : z ≠ q := fun h => hz (by simp [h])
    obtain ⟨x, hx⟩ := hsurj z
    dsimp [f] at hx
    split_ifs at hx with hxa hxb
    · exact (hzp hx.symm).elim
    · exact (hzq hx.symm).elim
    · exact ⟨x, hmem hxa hxb, hx⟩

end SunTwoDeletion
