import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_9_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 2
    (![4, 8, 6, 7, 3, 5] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 3
    (![7, 5, 4, 2, 8, 6] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 4
    (![6, 5, 8, 7, 3, 2] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 5
    (![8, 6, 7, 2, 4, 3] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 6
    (![7, 8, 4, 5, 2, 3] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 7
    (![6, 8, 2, 4, 3, 5] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

theorem finite_9_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 9)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 6) 0 1 8
    (![3, 7, 5, 6, 2, 4] : Fin 6 → ZMod 9)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
