import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_19_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 2
    (![10, 8, 6, 4, 18, 16, 14, 12, 11, 13, 15, 17, 3, 5, 7, 9] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 3
    (![5, 2, 18, 15, 12, 17, 14, 11, 8, 16, 6, 9, 4, 7, 10, 13] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 4
    (![11, 17, 10, 16, 6, 12, 18, 5, 8, 2, 15, 9, 3, 13, 7, 14] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 5
    (![2, 10, 18, 7, 15, 8, 16, 13, 17, 9, 12, 4, 11, 3, 14, 6] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 6
    (![12, 3, 13, 4, 14, 10, 11, 2, 7, 16, 15, 5, 9, 18, 8, 17] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 7
    (![11, 17, 4, 10, 16, 6, 12, 18, 5, 8, 2, 15, 9, 3, 13, 14] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 8
    (![16, 4, 11, 18, 6, 7, 14, 2, 9, 3, 15, 13, 12, 5, 17, 10] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 9
    (![2, 10, 18, 7, 15, 8, 16, 5, 13, 17, 12, 4, 11, 3, 14, 6] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 10
    (![15, 16, 17, 18, 11, 12, 13, 14, 5, 4, 3, 2, 9, 8, 7, 6] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 11
    (![12, 3, 13, 4, 14, 10, 2, 7, 16, 6, 15, 5, 9, 18, 8, 17] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 12
    (![17, 9, 4, 11, 3, 14, 6, 2, 10, 18, 7, 15, 8, 16, 5, 13] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 13
    (![12, 18, 5, 11, 17, 7, 6, 9, 3, 16, 10, 4, 14, 8, 2, 15] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 14
    (![3, 15, 8, 13, 12, 5, 17, 10, 16, 4, 11, 18, 6, 7, 2, 9] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 15
    (![12, 3, 13, 4, 14, 10, 11, 2, 7, 16, 6, 5, 9, 18, 8, 17] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 16
    (![2, 10, 18, 7, 15, 8, 5, 13, 17, 9, 12, 4, 11, 3, 14, 6] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 17
    (![4, 14, 11, 16, 13, 10, 7, 15, 18, 2, 5, 8, 3, 6, 9, 12] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

theorem finite_19_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 19)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 16) 0 1 18
    (![9, 7, 5, 3, 17, 15, 13, 11, 10, 12, 14, 16, 2, 4, 6, 8] : Fin 16 → ZMod 19)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
