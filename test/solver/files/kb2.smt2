(set-logic QF_LRA)
(declare-const BAL.3EBW Real)
(declare-const BHC.3EBW Real)
(declare-const BLC.3EBW Real)
(declare-const BLV.3EBW Real)
(declare-const BN4.3EBW Real)
(declare-const BP8.3EBW Real)
(declare-const BTO.3EBW Real)
(declare-const BAL.3PBW Real)
(declare-const BHC.3PBW Real)
(declare-const BLC.3PBW Real)
(declare-const BLV.3PBW Real)
(declare-const BN4.3PBW Real)
(declare-const BP8.3PBW Real)
(declare-const BTO.3PBW Real)
(declare-const BAL.3RBW Real)
(declare-const BHC.3RBW Real)
(declare-const BLC.3RBW Real)
(declare-const BLV.3RBW Real)
(declare-const BN4.3RBW Real)
(declare-const BP8.3RBW Real)
(declare-const BTO.3RBW Real)
(declare-const D3T...BW Real)
(declare-const EAL...BW Real)
(declare-const EHC...BW Real)
(declare-const ELC...BW Real)
(declare-const ELV...BW Real)
(declare-const EN4...BW Real)
(declare-const EP8...BW Real)
(declare-const ETO...BW Real)
(declare-const M3..3TBW Real)
(declare-const QPB73EBW Real)
(declare-const QVO73EBW Real)
(declare-const QVO73PBW Real)
(declare-const QPB73RBW Real)
(declare-const QVO73RBW Real)
(declare-const WMO73EBW Real)
(declare-const WRO73EBW Real)
(declare-const WMO73PBW Real)
(declare-const WRO73PBW Real)
(declare-const WMO73RBW Real)
(declare-const WRO73RBW Real)
(assert (<= 0 BAL.3EBW))
(assert (and (<= 0 BHC.3EBW) (<= BHC.3EBW 10)))
(assert (<= 0 BLC.3EBW))
(assert (<= 0 BLV.3EBW))
(assert (<= 0 BN4.3EBW))
(assert (<= 0 BP8.3EBW))
(assert (<= 0 BTO.3EBW))
(assert (<= 0 BAL.3PBW))
(assert (<= 0 BHC.3PBW))
(assert (<= 0 BLC.3PBW))
(assert (<= 0 BLV.3PBW))
(assert (<= 0 BN4.3PBW))
(assert (<= 0 BP8.3PBW))
(assert (<= 0 BTO.3PBW))
(assert (<= 0 BAL.3RBW))
(assert (<= 0 BHC.3RBW))
(assert (<= 0 BLC.3RBW))
(assert (<= 0 BLV.3RBW))
(assert (<= 0 BN4.3RBW))
(assert (<= 0 BP8.3RBW))
(assert (<= 0 BTO.3RBW))
(assert (and (<= 0 D3T...BW) (<= D3T...BW 200)))
(assert (and (<= 0 EAL...BW) (<= EAL...BW 10)))
(assert (and (<= 0 EHC...BW) (<= EHC...BW 20)))
(assert (and (<= 0 ELC...BW) (<= ELC...BW 25)))
(assert (and (<= 0 ELV...BW) (<= ELV...BW 12)))
(assert (and (<= 0 EN4...BW) (<= EN4...BW 100)))
(assert (and (<= 0 EP8...BW) (<= EP8...BW 35)))
(assert (and (<= 0 ETO...BW) (<= ETO...BW 5)))
(assert (<= 0 M3..3TBW))
(assert (<= 0 QPB73EBW))
(assert (<= 0 QVO73EBW))
(assert (<= 0 QVO73PBW))
(assert (<= 0 QPB73RBW))
(assert (<= 0 QVO73RBW))
(assert (<= 0 WMO73EBW))
(assert (<= 0 WRO73EBW))
(assert (<= 0 WMO73PBW))
(assert (<= 0 WRO73PBW))
(assert (<= 0 WMO73RBW))
(assert (<= 0 WRO73RBW))
(assert (= (+ (* (- 1) BAL.3EBW) (* (- 1) BAL.3PBW) (* (- 1) BAL.3RBW) EAL...BW) 0))
(assert (= (+ (* (- 1) BHC.3EBW) (* (- 1) BHC.3PBW) (* (- 1) BHC.3RBW) EHC...BW) 0))
(assert (= (+ (* (- 1) BLC.3EBW) (* (- 1) BLC.3PBW) (* (- 1) BLC.3RBW) ELC...BW) 0))
(assert (= (+ (* (- 1) BLV.3EBW) (* (- 1) BLV.3PBW) (* (- 1) BLV.3RBW) ELV...BW) 0))
(assert (= (+ (* (- 1) BN4.3EBW) (* (- 1) BN4.3PBW) (* (- 1) BN4.3RBW) EN4...BW) 0))
(assert (= (+ (* (- 1) BP8.3EBW) (* (- 1) BP8.3PBW) (* (- 1) BP8.3RBW) EP8...BW) 0))
(assert (= (+ (* (- 1) BTO.3EBW) (* (- 1) BTO.3PBW) (* (- 1) BTO.3RBW) ETO...BW) 0))
(assert (= (+ (* (- 0.29) M3..3TBW) QVO73EBW) 0))
(assert (= (+ (* (- 0.17) M3..3TBW) QVO73PBW) 0))
(assert (= (+ (* (- 0.54) M3..3TBW) QVO73RBW) 0))
(assert (= (+ (* (- 1) D3T...BW) M3..3TBW) 0))
(assert (= (+ BAL.3EBW BHC.3EBW BLC.3EBW BLV.3EBW BN4.3EBW BP8.3EBW BTO.3EBW (* (- 1) QVO73EBW)) 0))
(assert (= (+ BAL.3PBW BHC.3PBW BLC.3PBW BLV.3PBW BN4.3PBW BP8.3PBW BTO.3PBW (* (- 1) QVO73PBW)) 0))
(assert (= (+ BAL.3RBW BHC.3RBW BLC.3RBW BLV.3RBW BN4.3RBW BP8.3RBW BTO.3RBW (* (- 1) QVO73RBW)) 0))
(assert (>= (+ (* 99.18559 BAL.3EBW) (* 82.04308 BHC.3EBW) (* 83.9937 BLC.3EBW) (* 85.61385 BLV.3EBW) (* 98.06433 BN4.3EBW) (* 91.62642 BP8.3EBW) (* 90.49629 BTO.3EBW) (* 1.23842 QPB73EBW) (* (- 2.10531) QVO73EBW) (* (- 1) WMO73EBW)) 0))
(assert (>= (+ (* 94.63568 BAL.3EBW) (* 79.40534 BHC.3EBW) (* 80.37873 BLC.3EBW) (* 80.36789 BLV.3EBW) (* 92.71594 BN4.3EBW) (* 90.03844 BP8.3EBW) (* 89.10432 BTO.3EBW) (* 3.42918 QPB73EBW) (* (- 1.37167) QVO73EBW) (* (- 1) WMO73EBW)) 0))
(assert (>= (+ (* 98.08976 BAL.3EBW) (* 81.47009 BHC.3EBW) (* 83.22026 BLC.3EBW) (* 84.5191 BLV.3EBW) (* 96.86628 BN4.3EBW) (* 91.26611 BP8.3EBW) (* 90.14887 BTO.3EBW) (* 1.55751 QPB73EBW) (* (- 2.02477) QVO73EBW) (* (- 1) WMO73EBW)) 0))
(assert (>= (+ (* 103.0581 BAL.3EBW) (* 95.02163 BHC.3EBW) (* 98.64634 BLC.3EBW) (* 88.46612 BLV.3EBW) (* 101.66321 BN4.3EBW) (* 102.51818 BP8.3EBW) (* 106.46719 BTO.3EBW) (* 1.27141 QPB73EBW) (* (- 2.16139) QVO73EBW) (* (- 1) WRO73EBW)) 0))
(assert (>= (+ (* 98.70277 BAL.3EBW) (* 92.89535 BHC.3EBW) (* 95.38345 BLC.3EBW) (* 82.8797 BLV.3EBW) (* 97.32996 BN4.3EBW) (* 101.17309 BP8.3EBW) (* 105.47666 BTO.3EBW) (* 2.52143 QPB73EBW) (* (- 1.00857) QVO73EBW) (* (- 1) WRO73EBW)) 0))
(assert (>= (+ (* 102.02191 BAL.3EBW) (* 94.57094 BHC.3EBW) (* 97.97965 BLC.3EBW) (* 87.33298 BLV.3EBW) (* 100.65 BN4.3EBW) (* 102.21363 BP8.3EBW) (* 106.21918 BTO.3EBW) (* 1.54954 QPB73EBW) (* (- 2.0144) QVO73EBW) (* (- 1) WRO73EBW)) 0))
(assert (>= (+ (* 99.18559 BAL.3RBW) (* 82.04308 BHC.3RBW) (* 83.9937 BLC.3RBW) (* 85.61385 BLV.3RBW) (* 98.06433 BN4.3RBW) (* 91.62642 BP8.3RBW) (* 90.49629 BTO.3RBW) (* 1.75028 QPB73RBW) (* (- 2.97548) QVO73RBW) (* (- 1) WMO73RBW)) 0))
(assert (>= (+ (* 95.17073 BAL.3RBW) (* 79.72867 BHC.3RBW) (* 80.82888 BLC.3RBW) (* 81.03825 BLV.3RBW) (* 93.41749 BN4.3RBW) (* 90.22411 BP8.3RBW) (* 89.25587 BTO.3RBW) (* 4.41873 QPB73RBW) (* (- 2.20937) QVO73RBW) (* (- 1) WMO73RBW)) 0))
(assert (>= (+ (* 97.11016 BAL.3RBW) (* 80.94047 BHC.3RBW) (* 82.49926 BLC.3RBW) (* 83.48458 BLV.3RBW) (* 95.86635 BN4.3RBW) (* 90.94112 BP8.3RBW) (* 89.84584 BTO.3RBW) (* 2.74531 QPB73RBW) (* (- 2.74531) QVO73RBW) (* (- 1) WMO73RBW)) 0))
(assert (>= (+ (* 103.0581 BAL.3RBW) (* 95.02163 BHC.3RBW) (* 98.64634 BLC.3RBW) (* 88.46612 BLV.3RBW) (* 101.66321 BN4.3RBW) (* 102.51818 BP8.3RBW) (* 106.46719 BTO.3RBW) (* 1.64391 QPB73RBW) (* (- 2.79464) QVO73RBW) (* (- 1) WRO73RBW)) 0))
(assert (>= (+ (* 99.19039 BAL.3RBW) (* 93.16124 BHC.3RBW) (* 95.80861 BLC.3RBW) (* 83.61375 BLV.3RBW) (* 97.86876 BN4.3RBW) (* 101.32905 BP8.3RBW) (* 105.58392 BTO.3RBW) (* 4.31949 QPB73RBW) (* (- 2.15975) QVO73RBW) (* (- 1) WRO73RBW)) 0))
(assert (>= (+ (* 101.0885 BAL.3RBW) (* 94.14769 BHC.3RBW) (* 97.34183 BLC.3RBW) (* 86.24515 BLV.3RBW) (* 99.77765 BN4.3RBW) (* 101.93754 BP8.3RBW) (* 106.0019 BTO.3RBW) (* 2.62696 QPB73RBW) (* (- 2.62696) QVO73RBW) (* (- 1) WRO73RBW)) 0))
(assert (>= (+ (* (- 107.52) QVO73EBW) (* 0.73 WMO73EBW) (* 0.41 WRO73EBW)) 0))
(assert (>= (+ (* (- 97.41) QVO73PBW) (* 0.84 WMO73PBW) (* 0.27 WRO73PBW)) 0))
(assert (>= (+ (* (- 98.5) QVO73RBW) (* 0.81 WMO73RBW) (* 0.31 WRO73RBW)) 0))
(assert (= (+ (* 91.96313 BAL.3PBW) (* 78.09095 BHC.3PBW) (* 80.74635 BLC.3PBW) (* 77.37441 BLV.3PBW) (* 88.35436 BN4.3PBW) (* 88.58029 BP8.3PBW) (* 88.18188 BTO.3PBW) (* (- 1) WMO73PBW)) 0))
(assert (= (+ (* 96.13556 BAL.3PBW) (* 90.99637 BHC.3PBW) (* 93.95665 BLC.3PBW) (* 79.78002 BLV.3PBW) (* 94.11062 BN4.3PBW) (* 99.83178 BP8.3PBW) (* 105.07558 BTO.3PBW) (* (- 1) WRO73PBW)) 0))
(assert (<= (+ QPB73EBW (* (- 1.5) QVO73EBW) (* (- 1.5) QVO73PBW) QPB73RBW (* (- 1.5) QVO73RBW)) 0))
(assert (<= (+ (* 6 BAL.3EBW) (* (- 2) BHC.3EBW) (* 7 BLC.3EBW) (* 14 BLV.3EBW) (* 80 BN4.3EBW) (* 4 BP8.3EBW) (* (- 1) BTO.3EBW) (* (- 16) QVO73EBW)) 0))
(assert (<= (+ QPB73EBW (* (- 1.7) QVO73EBW)) 0))
(assert (<= (+ (* 4 BAL.3EBW) (* 0.5 BHC.3EBW) (* 4.5 BLC.3EBW) (* 7.2 BLV.3EBW) (* 70 BN4.3EBW) (* 3.6 BP8.3EBW) (* 1.2 BTO.3EBW) (* (- 12) QVO73EBW)) 0))
(assert (<= (+ (* 50.3 BAL.3EBW) (* (- 15.6) BHC.3EBW) (* 57.9 BLC.3EBW) (* 102.3 BLV.3EBW) (* 113 BN4.3EBW) (* 28.9 BP8.3EBW) (* 5 BTO.3EBW) (* (- 61) QVO73EBW)) 0))
(assert (<= (+ (* 6 BAL.3PBW) (* (- 2) BHC.3PBW) (* 7 BLC.3PBW) (* 14 BLV.3PBW) (* 80 BN4.3PBW) (* 4 BP8.3PBW) (* (- 1) BTO.3PBW) (* (- 16) QVO73PBW)) 0))
(assert (<= (+ (* 4 BAL.3PBW) (* 0.5 BHC.3PBW) (* 4.5 BLC.3PBW) (* 7.2 BLV.3PBW) (* 70 BN4.3PBW) (* 3.6 BP8.3PBW) (* 1.2 BTO.3PBW) (* (- 12) QVO73PBW)) 0))
(assert (<= (+ (* 50.3 BAL.3PBW) (* (- 15.6) BHC.3PBW) (* 57.9 BLC.3PBW) (* 102.3 BLV.3PBW) (* 113 BN4.3PBW) (* 28.9 BP8.3PBW) (* 5 BTO.3PBW) (* (- 61) QVO73PBW)) 0))
(assert (<= (+ (* 6 BAL.3RBW) (* (- 2) BHC.3RBW) (* 7 BLC.3RBW) (* 14 BLV.3RBW) (* 80 BN4.3RBW) (* 4 BP8.3RBW) (* (- 1) BTO.3RBW) (* (- 16) QVO73RBW)) 0))
(assert (<= (+ QPB73RBW (* (- 1.7) QVO73RBW)) 0))
(assert (<= (+ (* 4 BAL.3RBW) (* 0.5 BHC.3RBW) (* 4.5 BLC.3RBW) (* 7.2 BLV.3RBW) (* 70 BN4.3RBW) (* 3.6 BP8.3RBW) (* 1.2 BTO.3RBW) (* (- 12) QVO73RBW)) 0))
(assert (<= (+ (* 50.3 BAL.3RBW) (* (- 15.6) BHC.3RBW) (* 57.9 BLC.3RBW) (* 102.3 BLV.3RBW) (* 113 BN4.3RBW) (* 28.9 BP8.3RBW) (* 5 BTO.3RBW) (* (- 61) QVO73RBW)) 0))
(check-sat)
