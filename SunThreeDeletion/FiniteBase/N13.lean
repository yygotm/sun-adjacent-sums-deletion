import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_13_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 2
    (![6, 4, 12, 10, 8, 9, 11, 3, 5, 7] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 3
    (![9, 11, 5, 7, 6, 4, 2, 12, 10, 8] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 4
    (![11, 10, 6, 12, 5, 2, 9, 3, 7, 8] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 5
    (![11, 6, 8, 3, 12, 4, 9, 10, 2, 7] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 6
    (![9, 8, 7, 12, 11, 10, 4, 5, 2, 3] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 7
    (![11, 12, 8, 9, 10, 3, 2, 6, 5, 4] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 8
    (![10, 9, 12, 11, 5, 6, 7, 2, 3, 4] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 9
    (![2, 10, 5, 4, 12, 7, 3, 8, 6, 11] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 10
    (![6, 9, 8, 3, 11, 7, 12, 4, 5, 2] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 11
    (![8, 10, 12, 2, 4, 6, 5, 3, 9, 7] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

theorem finite_13_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 13)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 10) 0 1 12
    (![5, 3, 11, 9, 7, 8, 10, 2, 4, 6] : Fin 10 → ZMod 13)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
