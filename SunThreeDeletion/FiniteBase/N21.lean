import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_21_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 2
    (![10, 8, 6, 4, 20, 18, 16, 14, 12, 13, 15, 17, 19, 3, 5, 7, 9, 11] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 3
    (![9, 10, 11, 12, 13, 4, 5, 6, 7, 8, 18, 17, 16, 15, 14, 2, 20, 19] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 4
    (![10, 11, 12, 13, 14, 5, 6, 7, 8, 9, 19, 18, 17, 16, 15, 3, 2, 20] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 5
    (![6, 14, 9, 17, 8, 16, 3, 11, 19, 15, 7, 20, 12, 4, 13, 18, 10, 2] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 6
    (![9, 14, 19, 3, 8, 5, 10, 15, 20, 4, 12, 7, 2, 18, 13, 16, 11, 17] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 7
    (![19, 2, 4, 6, 9, 11, 13, 15, 17, 16, 14, 12, 10, 8, 5, 3, 20, 18] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 8
    (![16, 13, 5, 14, 6, 19, 11, 3, 7, 15, 2, 10, 18, 9, 17, 4, 12, 20] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 9
    (![6, 14, 17, 8, 16, 3, 11, 19, 15, 7, 20, 12, 4, 13, 5, 18, 10, 2] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 10
    (![4, 15, 5, 16, 6, 12, 2, 13, 3, 14, 19, 8, 18, 7, 17, 11, 20, 9] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 11
    (![17, 18, 19, 20, 12, 13, 14, 15, 16, 5, 4, 3, 2, 10, 9, 8, 7, 6] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 12
    (![3, 14, 4, 15, 5, 11, 2, 13, 18, 7, 17, 6, 16, 10, 20, 9, 19, 8] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 13
    (![7, 15, 2, 10, 18, 9, 17, 4, 12, 20, 16, 8, 5, 14, 6, 19, 11, 3] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 14
    (![15, 7, 20, 12, 4, 13, 5, 18, 10, 2, 6, 9, 17, 8, 16, 3, 11, 19] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 15
    (![6, 8, 10, 12, 14, 17, 19, 2, 4, 3, 20, 18, 16, 13, 11, 9, 7, 5] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 16
    (![10, 15, 20, 4, 9, 6, 11, 5, 13, 8, 3, 19, 14, 17, 12, 7, 2, 18] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 17
    (![18, 7, 6, 16, 10, 20, 9, 19, 8, 3, 14, 4, 15, 5, 11, 12, 2, 13] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 18
    (![3, 4, 5, 6, 7, 19, 20, 2, 12, 11, 10, 9, 8, 17, 16, 15, 14, 13] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 19
    (![4, 5, 6, 7, 8, 20, 2, 3, 13, 12, 11, 10, 9, 18, 17, 16, 15, 14] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

theorem finite_21_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 21)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 18) 0 1 20
    (![9, 7, 5, 3, 19, 17, 15, 13, 11, 12, 14, 16, 18, 2, 4, 6, 8, 10] : Fin 18 → ZMod 21)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
