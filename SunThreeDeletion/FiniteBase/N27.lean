import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_27_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 2
    (![14, 12, 10, 8, 6, 4, 26, 24, 22, 20, 18, 16, 15, 17, 19, 21, 23, 25, 3, 5, 7, 9, 11, 13] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 3
    (![10, 11, 12, 13, 14, 15, 16, 4, 5, 6, 7, 8, 9, 23, 22, 21, 20, 19, 18, 17, 2, 26, 25, 24] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 4
    (![11, 12, 13, 14, 15, 16, 17, 5, 6, 7, 8, 9, 10, 24, 23, 22, 21, 20, 19, 18, 3, 2, 26, 25] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 5
    (![20, 15, 10, 22, 17, 23, 18, 13, 8, 3, 25, 9, 14, 19, 24, 2, 7, 12, 6, 11, 16, 21, 26, 4] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 6
    (![8, 13, 18, 23, 11, 5, 10, 15, 20, 25, 3, 19, 14, 9, 4, 26, 21, 16, 22, 17, 12, 7, 2, 24] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 7
    (![6, 26, 19, 12, 5, 25, 18, 21, 14, 20, 13, 23, 3, 10, 17, 24, 4, 11, 8, 15, 22, 2, 9, 16] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 8
    (![22, 2, 9, 16, 23, 3, 10, 7, 14, 21, 15, 5, 25, 18, 11, 4, 24, 17, 20, 13, 6, 26, 19, 12] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 9
    (![2, 10, 18, 26, 7, 15, 23, 8, 16, 24, 5, 13, 21, 25, 17, 20, 12, 4, 19, 11, 3, 22, 14, 6] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 10
    (![12, 2, 19, 9, 26, 16, 6, 18, 8, 25, 15, 5, 22, 17, 20, 3, 13, 23, 11, 21, 4, 14, 24, 7] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 11
    (![5, 21, 10, 26, 15, 4, 20, 17, 6, 22, 16, 24, 8, 19, 3, 14, 25, 9, 12, 23, 7, 18, 2, 13] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 12
    (![19, 20, 21, 22, 23, 24, 25, 13, 14, 15, 16, 17, 18, 5, 4, 3, 2, 26, 11, 10, 9, 8, 7, 6] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 13
    (![18, 5, 19, 6, 20, 7, 21, 15, 2, 16, 3, 17, 4, 11, 24, 10, 23, 9, 22, 8, 14, 26, 12, 25] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 14
    (![21, 22, 23, 24, 25, 26, 15, 16, 17, 18, 19, 20, 7, 6, 5, 4, 3, 2, 13, 12, 11, 10, 9, 8] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 15
    (![17, 4, 18, 5, 19, 6, 20, 14, 2, 16, 3, 10, 23, 9, 22, 8, 21, 7, 13, 26, 12, 25, 11, 24] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 16
    (![23, 24, 25, 26, 2, 17, 18, 19, 20, 21, 22, 9, 8, 7, 6, 5, 4, 3, 15, 14, 13, 12, 11, 10] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 17
    (![4, 20, 9, 25, 14, 3, 19, 16, 5, 21, 10, 26, 15, 23, 7, 18, 2, 13, 24, 8, 11, 22, 6, 12] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 18
    (![11, 8, 25, 15, 5, 17, 7, 24, 14, 4, 21, 16, 26, 9, 19, 2, 12, 22, 10, 20, 3, 13, 23, 6] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 19
    (![3, 11, 8, 16, 24, 9, 17, 25, 6, 14, 22, 26, 18, 10, 2, 21, 13, 5, 20, 12, 4, 23, 15, 7] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 20
    (![25, 17, 9, 12, 4, 19, 11, 3, 22, 14, 6, 2, 10, 18, 26, 7, 15, 23, 8, 16, 24, 5, 13, 21] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 21
    (![5, 25, 18, 11, 4, 24, 17, 20, 13, 6, 26, 19, 12, 22, 2, 9, 16, 23, 3, 10, 7, 14, 8, 15] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 22
    (![9, 14, 19, 24, 2, 7, 12, 6, 11, 16, 21, 26, 4, 20, 15, 10, 5, 17, 23, 18, 13, 8, 3, 25] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 23
    (![19, 14, 9, 4, 26, 21, 16, 22, 17, 12, 7, 2, 24, 8, 13, 18, 6, 11, 5, 10, 15, 20, 25, 3] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 24
    (![4, 5, 6, 7, 8, 9, 10, 25, 26, 2, 3, 17, 16, 15, 14, 13, 12, 11, 23, 22, 21, 20, 19, 18] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 25
    (![5, 6, 7, 8, 9, 10, 11, 26, 2, 3, 4, 18, 17, 16, 15, 14, 13, 12, 24, 23, 22, 21, 20, 19] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

theorem finite_27_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 27)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 24) 0 1 26
    (![13, 11, 9, 7, 5, 3, 25, 23, 21, 19, 17, 15, 14, 16, 18, 20, 22, 24, 2, 4, 6, 8, 10, 12] : Fin 24 → ZMod 27)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
