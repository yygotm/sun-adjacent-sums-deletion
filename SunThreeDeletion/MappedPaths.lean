import SunTwoDeletion.Paths
import SunTwoDeletion.Map
import Mathlib.Tactic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {H G : Type*} [AddCommGroup H] [AddCommGroup G] [Finite G]

noncomputable def path_of_mapped_cycle {A : Set H} (C : RainbowCycle A)
    (f : H →+ G) (hf : Function.Injective f) (r : G)
    (u v : H) (hu : u ∈ A) (hv : v ∈ A) (hclose : C.next v = u) :
    RainbowPath ((fun x => f x+r) '' A) (f u+r) (f v+r) := by
  let D := (C.map f hf).translate r
  have hset : (fun x : G => x+r) '' (f '' A) = (fun x => f x+r) '' A :=
    Set.image_image _ _ _
  have hstart : f u+r ∈ (fun x : G => x+r) '' (f '' A) :=
    ⟨f u, ⟨u,hu,rfl⟩, rfl⟩
  have hend : f v+r ∈ (fun x : G => x+r) '' (f '' A) :=
    ⟨f v, ⟨v,hv,rfl⟩, rfl⟩
  have hc : D.next (f v+r) = f u+r := by
    rw [RainbowCycle.translate_next, RainbowCycle.map_next, hclose]
  have p := RainbowPath.ofFiniteCycle D (f u+r) (f v+r) hstart hend hc
  exact hset ▸ p

end SunThreeDeletion

