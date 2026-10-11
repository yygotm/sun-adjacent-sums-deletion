import SunThreeDeletion.FiniteBase.N7
import SunThreeDeletion.FiniteBase.N9
import SunThreeDeletion.FiniteBase.N11
import SunThreeDeletion.FiniteBase.N13
import SunThreeDeletion.FiniteBase.N15
import SunThreeDeletion.FiniteBase.N17
import SunThreeDeletion.FiniteBase.N19
import SunThreeDeletion.FiniteBase.N21
import SunThreeDeletion.FiniteBase.N23
import SunThreeDeletion.FiniteBase.N25
import SunThreeDeletion.FiniteBase.N27
import SunThreeDeletion.FiniteBase.N29
import SunThreeDeletion.FiniteBase.N31
import SunThreeDeletion.FiniteBase.N33
import SunThreeDeletion.FiniteBase.N35
import SunThreeDeletion.FiniteBase.N37
import SunThreeDeletion.FiniteBase.N39
import SunThreeDeletion.FiniteBase.N41
import SunThreeDeletion.FiniteBase.N43
import SunThreeDeletion.FiniteBase.N45
import SunThreeDeletion.FiniteBase.N47

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_base_7 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 7) :
    HasRainbowCycle ({0, 1, (t : ZMod 7)}ᶜ : Set (ZMod 7)) := by
  interval_cases t
  · exact finite_7_2
  · exact finite_7_3
  · exact finite_7_4
  · exact finite_7_5
  · exact finite_7_6

theorem finite_base_9 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 9) :
    HasRainbowCycle ({0, 1, (t : ZMod 9)}ᶜ : Set (ZMod 9)) := by
  interval_cases t
  · exact finite_9_2
  · exact finite_9_3
  · exact finite_9_4
  · exact finite_9_5
  · exact finite_9_6
  · exact finite_9_7
  · exact finite_9_8

theorem finite_base_11 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 11) :
    HasRainbowCycle ({0, 1, (t : ZMod 11)}ᶜ : Set (ZMod 11)) := by
  interval_cases t
  · exact finite_11_2
  · exact finite_11_3
  · exact finite_11_4
  · exact finite_11_5
  · exact finite_11_6
  · exact finite_11_7
  · exact finite_11_8
  · exact finite_11_9
  · exact finite_11_10

theorem finite_base_13 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 13) :
    HasRainbowCycle ({0, 1, (t : ZMod 13)}ᶜ : Set (ZMod 13)) := by
  interval_cases t
  · exact finite_13_2
  · exact finite_13_3
  · exact finite_13_4
  · exact finite_13_5
  · exact finite_13_6
  · exact finite_13_7
  · exact finite_13_8
  · exact finite_13_9
  · exact finite_13_10
  · exact finite_13_11
  · exact finite_13_12

theorem finite_base_15 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 15) :
    HasRainbowCycle ({0, 1, (t : ZMod 15)}ᶜ : Set (ZMod 15)) := by
  interval_cases t
  · exact finite_15_2
  · exact finite_15_3
  · exact finite_15_4
  · exact finite_15_5
  · exact finite_15_6
  · exact finite_15_7
  · exact finite_15_8
  · exact finite_15_9
  · exact finite_15_10
  · exact finite_15_11
  · exact finite_15_12
  · exact finite_15_13
  · exact finite_15_14

theorem finite_base_17 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 17) :
    HasRainbowCycle ({0, 1, (t : ZMod 17)}ᶜ : Set (ZMod 17)) := by
  interval_cases t
  · exact finite_17_2
  · exact finite_17_3
  · exact finite_17_4
  · exact finite_17_5
  · exact finite_17_6
  · exact finite_17_7
  · exact finite_17_8
  · exact finite_17_9
  · exact finite_17_10
  · exact finite_17_11
  · exact finite_17_12
  · exact finite_17_13
  · exact finite_17_14
  · exact finite_17_15
  · exact finite_17_16

theorem finite_base_19 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 19) :
    HasRainbowCycle ({0, 1, (t : ZMod 19)}ᶜ : Set (ZMod 19)) := by
  interval_cases t
  · exact finite_19_2
  · exact finite_19_3
  · exact finite_19_4
  · exact finite_19_5
  · exact finite_19_6
  · exact finite_19_7
  · exact finite_19_8
  · exact finite_19_9
  · exact finite_19_10
  · exact finite_19_11
  · exact finite_19_12
  · exact finite_19_13
  · exact finite_19_14
  · exact finite_19_15
  · exact finite_19_16
  · exact finite_19_17
  · exact finite_19_18

theorem finite_base_21 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 21) :
    HasRainbowCycle ({0, 1, (t : ZMod 21)}ᶜ : Set (ZMod 21)) := by
  interval_cases t
  · exact finite_21_2
  · exact finite_21_3
  · exact finite_21_4
  · exact finite_21_5
  · exact finite_21_6
  · exact finite_21_7
  · exact finite_21_8
  · exact finite_21_9
  · exact finite_21_10
  · exact finite_21_11
  · exact finite_21_12
  · exact finite_21_13
  · exact finite_21_14
  · exact finite_21_15
  · exact finite_21_16
  · exact finite_21_17
  · exact finite_21_18
  · exact finite_21_19
  · exact finite_21_20

theorem finite_base_23 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 23) :
    HasRainbowCycle ({0, 1, (t : ZMod 23)}ᶜ : Set (ZMod 23)) := by
  interval_cases t
  · exact finite_23_2
  · exact finite_23_3
  · exact finite_23_4
  · exact finite_23_5
  · exact finite_23_6
  · exact finite_23_7
  · exact finite_23_8
  · exact finite_23_9
  · exact finite_23_10
  · exact finite_23_11
  · exact finite_23_12
  · exact finite_23_13
  · exact finite_23_14
  · exact finite_23_15
  · exact finite_23_16
  · exact finite_23_17
  · exact finite_23_18
  · exact finite_23_19
  · exact finite_23_20
  · exact finite_23_21
  · exact finite_23_22

theorem finite_base_25 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 25) :
    HasRainbowCycle ({0, 1, (t : ZMod 25)}ᶜ : Set (ZMod 25)) := by
  interval_cases t
  · exact finite_25_2
  · exact finite_25_3
  · exact finite_25_4
  · exact finite_25_5
  · exact finite_25_6
  · exact finite_25_7
  · exact finite_25_8
  · exact finite_25_9
  · exact finite_25_10
  · exact finite_25_11
  · exact finite_25_12
  · exact finite_25_13
  · exact finite_25_14
  · exact finite_25_15
  · exact finite_25_16
  · exact finite_25_17
  · exact finite_25_18
  · exact finite_25_19
  · exact finite_25_20
  · exact finite_25_21
  · exact finite_25_22
  · exact finite_25_23
  · exact finite_25_24

theorem finite_base_27 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 27) :
    HasRainbowCycle ({0, 1, (t : ZMod 27)}ᶜ : Set (ZMod 27)) := by
  interval_cases t
  · exact finite_27_2
  · exact finite_27_3
  · exact finite_27_4
  · exact finite_27_5
  · exact finite_27_6
  · exact finite_27_7
  · exact finite_27_8
  · exact finite_27_9
  · exact finite_27_10
  · exact finite_27_11
  · exact finite_27_12
  · exact finite_27_13
  · exact finite_27_14
  · exact finite_27_15
  · exact finite_27_16
  · exact finite_27_17
  · exact finite_27_18
  · exact finite_27_19
  · exact finite_27_20
  · exact finite_27_21
  · exact finite_27_22
  · exact finite_27_23
  · exact finite_27_24
  · exact finite_27_25
  · exact finite_27_26

theorem finite_base_29 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 29) :
    HasRainbowCycle ({0, 1, (t : ZMod 29)}ᶜ : Set (ZMod 29)) := by
  interval_cases t
  · exact finite_29_2
  · exact finite_29_3
  · exact finite_29_4
  · exact finite_29_5
  · exact finite_29_6
  · exact finite_29_7
  · exact finite_29_8
  · exact finite_29_9
  · exact finite_29_10
  · exact finite_29_11
  · exact finite_29_12
  · exact finite_29_13
  · exact finite_29_14
  · exact finite_29_15
  · exact finite_29_16
  · exact finite_29_17
  · exact finite_29_18
  · exact finite_29_19
  · exact finite_29_20
  · exact finite_29_21
  · exact finite_29_22
  · exact finite_29_23
  · exact finite_29_24
  · exact finite_29_25
  · exact finite_29_26
  · exact finite_29_27
  · exact finite_29_28

theorem finite_base_31 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 31) :
    HasRainbowCycle ({0, 1, (t : ZMod 31)}ᶜ : Set (ZMod 31)) := by
  interval_cases t
  · exact finite_31_2
  · exact finite_31_3
  · exact finite_31_4
  · exact finite_31_5
  · exact finite_31_6
  · exact finite_31_7
  · exact finite_31_8
  · exact finite_31_9
  · exact finite_31_10
  · exact finite_31_11
  · exact finite_31_12
  · exact finite_31_13
  · exact finite_31_14
  · exact finite_31_15
  · exact finite_31_16
  · exact finite_31_17
  · exact finite_31_18
  · exact finite_31_19
  · exact finite_31_20
  · exact finite_31_21
  · exact finite_31_22
  · exact finite_31_23
  · exact finite_31_24
  · exact finite_31_25
  · exact finite_31_26
  · exact finite_31_27
  · exact finite_31_28
  · exact finite_31_29
  · exact finite_31_30

theorem finite_base_33 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 33) :
    HasRainbowCycle ({0, 1, (t : ZMod 33)}ᶜ : Set (ZMod 33)) := by
  interval_cases t
  · exact finite_33_2
  · exact finite_33_3
  · exact finite_33_4
  · exact finite_33_5
  · exact finite_33_6
  · exact finite_33_7
  · exact finite_33_8
  · exact finite_33_9
  · exact finite_33_10
  · exact finite_33_11
  · exact finite_33_12
  · exact finite_33_13
  · exact finite_33_14
  · exact finite_33_15
  · exact finite_33_16
  · exact finite_33_17
  · exact finite_33_18
  · exact finite_33_19
  · exact finite_33_20
  · exact finite_33_21
  · exact finite_33_22
  · exact finite_33_23
  · exact finite_33_24
  · exact finite_33_25
  · exact finite_33_26
  · exact finite_33_27
  · exact finite_33_28
  · exact finite_33_29
  · exact finite_33_30
  · exact finite_33_31
  · exact finite_33_32

theorem finite_base_35 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 35) :
    HasRainbowCycle ({0, 1, (t : ZMod 35)}ᶜ : Set (ZMod 35)) := by
  interval_cases t
  · exact finite_35_2
  · exact finite_35_3
  · exact finite_35_4
  · exact finite_35_5
  · exact finite_35_6
  · exact finite_35_7
  · exact finite_35_8
  · exact finite_35_9
  · exact finite_35_10
  · exact finite_35_11
  · exact finite_35_12
  · exact finite_35_13
  · exact finite_35_14
  · exact finite_35_15
  · exact finite_35_16
  · exact finite_35_17
  · exact finite_35_18
  · exact finite_35_19
  · exact finite_35_20
  · exact finite_35_21
  · exact finite_35_22
  · exact finite_35_23
  · exact finite_35_24
  · exact finite_35_25
  · exact finite_35_26
  · exact finite_35_27
  · exact finite_35_28
  · exact finite_35_29
  · exact finite_35_30
  · exact finite_35_31
  · exact finite_35_32
  · exact finite_35_33
  · exact finite_35_34

theorem finite_base_37 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 37) :
    HasRainbowCycle ({0, 1, (t : ZMod 37)}ᶜ : Set (ZMod 37)) := by
  interval_cases t
  · exact finite_37_2
  · exact finite_37_3
  · exact finite_37_4
  · exact finite_37_5
  · exact finite_37_6
  · exact finite_37_7
  · exact finite_37_8
  · exact finite_37_9
  · exact finite_37_10
  · exact finite_37_11
  · exact finite_37_12
  · exact finite_37_13
  · exact finite_37_14
  · exact finite_37_15
  · exact finite_37_16
  · exact finite_37_17
  · exact finite_37_18
  · exact finite_37_19
  · exact finite_37_20
  · exact finite_37_21
  · exact finite_37_22
  · exact finite_37_23
  · exact finite_37_24
  · exact finite_37_25
  · exact finite_37_26
  · exact finite_37_27
  · exact finite_37_28
  · exact finite_37_29
  · exact finite_37_30
  · exact finite_37_31
  · exact finite_37_32
  · exact finite_37_33
  · exact finite_37_34
  · exact finite_37_35
  · exact finite_37_36

theorem finite_base_39 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 39) :
    HasRainbowCycle ({0, 1, (t : ZMod 39)}ᶜ : Set (ZMod 39)) := by
  interval_cases t
  · exact finite_39_2
  · exact finite_39_3
  · exact finite_39_4
  · exact finite_39_5
  · exact finite_39_6
  · exact finite_39_7
  · exact finite_39_8
  · exact finite_39_9
  · exact finite_39_10
  · exact finite_39_11
  · exact finite_39_12
  · exact finite_39_13
  · exact finite_39_14
  · exact finite_39_15
  · exact finite_39_16
  · exact finite_39_17
  · exact finite_39_18
  · exact finite_39_19
  · exact finite_39_20
  · exact finite_39_21
  · exact finite_39_22
  · exact finite_39_23
  · exact finite_39_24
  · exact finite_39_25
  · exact finite_39_26
  · exact finite_39_27
  · exact finite_39_28
  · exact finite_39_29
  · exact finite_39_30
  · exact finite_39_31
  · exact finite_39_32
  · exact finite_39_33
  · exact finite_39_34
  · exact finite_39_35
  · exact finite_39_36
  · exact finite_39_37
  · exact finite_39_38

theorem finite_base_41 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 41) :
    HasRainbowCycle ({0, 1, (t : ZMod 41)}ᶜ : Set (ZMod 41)) := by
  interval_cases t
  · exact finite_41_2
  · exact finite_41_3
  · exact finite_41_4
  · exact finite_41_5
  · exact finite_41_6
  · exact finite_41_7
  · exact finite_41_8
  · exact finite_41_9
  · exact finite_41_10
  · exact finite_41_11
  · exact finite_41_12
  · exact finite_41_13
  · exact finite_41_14
  · exact finite_41_15
  · exact finite_41_16
  · exact finite_41_17
  · exact finite_41_18
  · exact finite_41_19
  · exact finite_41_20
  · exact finite_41_21
  · exact finite_41_22
  · exact finite_41_23
  · exact finite_41_24
  · exact finite_41_25
  · exact finite_41_26
  · exact finite_41_27
  · exact finite_41_28
  · exact finite_41_29
  · exact finite_41_30
  · exact finite_41_31
  · exact finite_41_32
  · exact finite_41_33
  · exact finite_41_34
  · exact finite_41_35
  · exact finite_41_36
  · exact finite_41_37
  · exact finite_41_38
  · exact finite_41_39
  · exact finite_41_40

theorem finite_base_43 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 43) :
    HasRainbowCycle ({0, 1, (t : ZMod 43)}ᶜ : Set (ZMod 43)) := by
  interval_cases t
  · exact finite_43_2
  · exact finite_43_3
  · exact finite_43_4
  · exact finite_43_5
  · exact finite_43_6
  · exact finite_43_7
  · exact finite_43_8
  · exact finite_43_9
  · exact finite_43_10
  · exact finite_43_11
  · exact finite_43_12
  · exact finite_43_13
  · exact finite_43_14
  · exact finite_43_15
  · exact finite_43_16
  · exact finite_43_17
  · exact finite_43_18
  · exact finite_43_19
  · exact finite_43_20
  · exact finite_43_21
  · exact finite_43_22
  · exact finite_43_23
  · exact finite_43_24
  · exact finite_43_25
  · exact finite_43_26
  · exact finite_43_27
  · exact finite_43_28
  · exact finite_43_29
  · exact finite_43_30
  · exact finite_43_31
  · exact finite_43_32
  · exact finite_43_33
  · exact finite_43_34
  · exact finite_43_35
  · exact finite_43_36
  · exact finite_43_37
  · exact finite_43_38
  · exact finite_43_39
  · exact finite_43_40
  · exact finite_43_41
  · exact finite_43_42

theorem finite_base_45 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 45) :
    HasRainbowCycle ({0, 1, (t : ZMod 45)}ᶜ : Set (ZMod 45)) := by
  interval_cases t
  · exact finite_45_2
  · exact finite_45_3
  · exact finite_45_4
  · exact finite_45_5
  · exact finite_45_6
  · exact finite_45_7
  · exact finite_45_8
  · exact finite_45_9
  · exact finite_45_10
  · exact finite_45_11
  · exact finite_45_12
  · exact finite_45_13
  · exact finite_45_14
  · exact finite_45_15
  · exact finite_45_16
  · exact finite_45_17
  · exact finite_45_18
  · exact finite_45_19
  · exact finite_45_20
  · exact finite_45_21
  · exact finite_45_22
  · exact finite_45_23
  · exact finite_45_24
  · exact finite_45_25
  · exact finite_45_26
  · exact finite_45_27
  · exact finite_45_28
  · exact finite_45_29
  · exact finite_45_30
  · exact finite_45_31
  · exact finite_45_32
  · exact finite_45_33
  · exact finite_45_34
  · exact finite_45_35
  · exact finite_45_36
  · exact finite_45_37
  · exact finite_45_38
  · exact finite_45_39
  · exact finite_45_40
  · exact finite_45_41
  · exact finite_45_42
  · exact finite_45_43
  · exact finite_45_44

theorem finite_base_47 (t : ℕ) (ht : 2 ≤ t) (hlt : t < 47) :
    HasRainbowCycle ({0, 1, (t : ZMod 47)}ᶜ : Set (ZMod 47)) := by
  interval_cases t
  · exact finite_47_2
  · exact finite_47_3
  · exact finite_47_4
  · exact finite_47_5
  · exact finite_47_6
  · exact finite_47_7
  · exact finite_47_8
  · exact finite_47_9
  · exact finite_47_10
  · exact finite_47_11
  · exact finite_47_12
  · exact finite_47_13
  · exact finite_47_14
  · exact finite_47_15
  · exact finite_47_16
  · exact finite_47_17
  · exact finite_47_18
  · exact finite_47_19
  · exact finite_47_20
  · exact finite_47_21
  · exact finite_47_22
  · exact finite_47_23
  · exact finite_47_24
  · exact finite_47_25
  · exact finite_47_26
  · exact finite_47_27
  · exact finite_47_28
  · exact finite_47_29
  · exact finite_47_30
  · exact finite_47_31
  · exact finite_47_32
  · exact finite_47_33
  · exact finite_47_34
  · exact finite_47_35
  · exact finite_47_36
  · exact finite_47_37
  · exact finite_47_38
  · exact finite_47_39
  · exact finite_47_40
  · exact finite_47_41
  · exact finite_47_42
  · exact finite_47_43
  · exact finite_47_44
  · exact finite_47_45
  · exact finite_47_46

theorem cyclic_finite_base (m t : ℕ) (hm : 7 ≤ m) (hmax : m ≤ 47) (hodd : Odd m)
    (ht : 2 ≤ t) (hlt : t < m) :
    HasRainbowCycle ({0, 1, (t : ZMod m)}ᶜ : Set (ZMod m)) := by
  interval_cases m
  · exact finite_base_7 t ht hlt
  · norm_num at hodd
  · exact finite_base_9 t ht hlt
  · norm_num at hodd
  · exact finite_base_11 t ht hlt
  · norm_num at hodd
  · exact finite_base_13 t ht hlt
  · norm_num at hodd
  · exact finite_base_15 t ht hlt
  · norm_num at hodd
  · exact finite_base_17 t ht hlt
  · norm_num at hodd
  · exact finite_base_19 t ht hlt
  · norm_num at hodd
  · exact finite_base_21 t ht hlt
  · norm_num at hodd
  · exact finite_base_23 t ht hlt
  · norm_num at hodd
  · exact finite_base_25 t ht hlt
  · norm_num at hodd
  · exact finite_base_27 t ht hlt
  · norm_num at hodd
  · exact finite_base_29 t ht hlt
  · norm_num at hodd
  · exact finite_base_31 t ht hlt
  · norm_num at hodd
  · exact finite_base_33 t ht hlt
  · norm_num at hodd
  · exact finite_base_35 t ht hlt
  · norm_num at hodd
  · exact finite_base_37 t ht hlt
  · norm_num at hodd
  · exact finite_base_39 t ht hlt
  · norm_num at hodd
  · exact finite_base_41 t ht hlt
  · norm_num at hodd
  · exact finite_base_43 t ht hlt
  · norm_num at hodd
  · exact finite_base_45 t ht hlt
  · norm_num at hodd
  · exact finite_base_47 t ht hlt

end SunThreeDeletion
