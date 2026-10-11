import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_17_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 2
    (![8, 6, 4, 16, 14, 12, 10, 11, 13, 15, 3, 5, 7, 9] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 3
    (![8, 9, 10, 11, 4, 5, 6, 7, 15, 14, 13, 12, 2, 16] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 4
    (![15, 7, 3, 6, 9, 12, 2, 16, 13, 10, 14, 11, 8, 5] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 5
    (![10, 12, 13, 8, 3, 15, 9, 14, 2, 7, 6, 11, 16, 4] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 6
    (![5, 16, 10, 4, 12, 11, 14, 3, 9, 15, 7, 13, 2, 8] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 7
    (![12, 13, 14, 15, 8, 9, 10, 11, 2, 16, 6, 5, 4, 3] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 8
    (![12, 4, 13, 5, 10, 2, 11, 3, 7, 15, 6, 14, 9, 16] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 9
    (![14, 15, 16, 10, 11, 12, 13, 4, 3, 2, 8, 7, 6, 5] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 10
    (![11, 3, 12, 4, 9, 2, 6, 14, 5, 13, 8, 16, 7, 15] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 11
    (![16, 2, 12, 13, 14, 15, 6, 5, 4, 3, 10, 9, 8, 7] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 12
    (![4, 15, 9, 3, 11, 5, 16, 10, 13, 2, 8, 14, 6, 7] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 13
    (![9, 4, 16, 11, 12, 7, 2, 14, 8, 6, 5, 10, 15, 3] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 14
    (![16, 2, 5, 8, 4, 7, 10, 13, 3, 11, 15, 12, 9, 6] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 15
    (![3, 4, 5, 6, 16, 2, 10, 9, 8, 7, 14, 13, 12, 11] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

theorem finite_17_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 17)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 14) 0 1 16
    (![7, 5, 3, 15, 13, 11, 9, 10, 12, 14, 2, 4, 6, 8] : Fin 14 → ZMod 17)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
