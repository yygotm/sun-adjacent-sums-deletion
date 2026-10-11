import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_11_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 2
    (![6, 4, 10, 8, 7, 9, 3, 5] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 3
    (![7, 9, 5, 6, 4, 2, 10, 8] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 4
    (![6, 3, 9, 2, 5, 8, 7, 10] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 5
    (![8, 7, 6, 10, 9, 3, 4, 2] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 6
    (![9, 10, 7, 8, 3, 2, 5, 4] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 7
    (![9, 8, 10, 4, 5, 6, 2, 3] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 8
    (![10, 7, 4, 5, 2, 6, 9, 3] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 9
    (![6, 8, 10, 2, 4, 5, 3, 7] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

theorem finite_11_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 11)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 8) 0 1 10
    (![5, 3, 9, 7, 6, 8, 2, 4] : Fin 8 → ZMod 11)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
