import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SunThreeDeletion
open SunTwoDeletion

theorem base_C9_line : HasRainbowCycle ({0,3,6}ᶜ : Set (ZMod 9)) :=
  three_cycle_of_certificate (by decide : 2 ≤ 6) 0 3 6
    (![1,2,5,8,7,4] : Fin 6 → ZMod 9) (by decide) (by decide) (by decide)

theorem base_C15_line : HasRainbowCycle ({0,3,6}ᶜ : Set (ZMod 15)) :=
  three_cycle_of_certificate (by decide : 2 ≤ 12) 0 3 6
    (![1,2,4,5,7,8,9,11,14,12,10,13] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem base_C25_line : HasRainbowCycle ({0,5,10}ᶜ : Set (ZMod 25)) :=
  three_cycle_of_certificate (by decide : 2 ≤ 22) 0 5 10
    (![1,2,3,4,6,7,8,9,11,12,13,14,15,16,18,19,17,22,21,20,24,23] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem base_C3xC3_line :
    HasRainbowCycle ({(0,0),(1,0),(2,0)}ᶜ : Set (ZMod 3 × ZMod 3)) :=
  cycle_of_certificate (by decide : 2 ≤ 6)
    (![(0,1),(1,1),(2,1),(0,2),(2,2),(1,2)] : Fin 6 → ZMod 3 × ZMod 3)
    _ (by decide) (by decide) (by decide)

theorem base_C3xC3_independent :
    HasRainbowCycle ({(0,0),(1,0),(0,1)}ᶜ : Set (ZMod 3 × ZMod 3)) :=
  cycle_of_certificate (by decide : 2 ≤ 6)
    (![(2,0),(1,1),(2,1),(1,2),(0,2),(2,2)] : Fin 6 → ZMod 3 × ZMod 3)
    _ (by decide) (by decide) (by decide)

theorem base_C5xC5_line :
    HasRainbowCycle ({(0,0),(1,0),(2,0)}ᶜ : Set (ZMod 5 × ZMod 5)) :=
  cycle_of_certificate (by decide : 2 ≤ 22)
    (![(3,0),(4,0),(0,1),(1,1),(2,1),(3,1),(4,1),(0,2),(1,2),(2,2),(3,2),
      (0,3),(4,2),(1,3),(2,3),(3,3),(4,3),(0,4),(1,4),(2,4),(3,4),(4,4)] :
      Fin 22 → ZMod 5 × ZMod 5)
    _ (by decide) (by decide) (by decide)

end SunThreeDeletion

