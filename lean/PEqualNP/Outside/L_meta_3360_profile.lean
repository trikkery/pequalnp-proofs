import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3360_profile

def edges : List Nat := [1,12,23,34,40,5,16,27,38,57,68,85]

def target (input : Fin 9 → Bool) : Bool :=
  edges.any fun e => input (Fin.ofNat 9 (e / 10)) && input (Fin.ofNat 9 (e % 10))

def row (i j k pattern outside : Nat) (v : Fin 9) : Bool :=
  if v.val = i then pattern.testBit 0
  else if v.val = j then pattern.testBit 1
  else if v.val = k then pattern.testBit 2
  else decide (v.val = outside)

def columns (i j k : Nat) : List Nat :=
  9 :: (List.range 9).filter (fun v => v != i && v != j && v != k)

def signature (i j k pattern : Nat) : List Bool :=
  (columns i j k).map fun outside => target (row i j k pattern outside)

def profileCount (i j k : Nat) : Nat :=
  ((List.range 8).map (signature i j k)).eraseDups.length

def slice (i : Nat) : List Nat :=
  (List.range 9).flatMap fun j =>
    if i < j then ((List.range 9).filter (fun k => decide (j < k))).map (profileCount i j)
    else []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice0 : slice 0 = [6, 7, 6, 6, 6, 7, 7, 7, 6, 7, 8, 6, 8, 5, 7, 7, 7, 7, 6, 7, 7, 6, 7, 6, 6, 8, 6, 8] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice1 : slice 1 = [6, 7, 7, 6, 6, 7, 6, 8, 6, 8, 7, 8, 7, 8, 7, 6, 6, 7, 7, 5, 7] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice2 : slice 2 = [6, 7, 7, 6, 6, 7, 8, 7, 8, 7, 5, 7, 7, 6, 6] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice3 : slice 3 = [6, 7, 7, 6, 8, 6, 6, 8, 6, 7] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice4 : slice 4 = [8, 7, 7, 8, 7, 8] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice5 : slice 5 = [7, 6, 6] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice6 : slice 6 = [7] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice7 : slice 7 = [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice8 : slice 8 = [] := by decide

def allCounts : List Nat :=
  slice 0 ++ slice 1 ++ slice 2 ++ slice 3 ++ slice 4 ++ slice 5 ++ slice 6 ++ slice 7 ++ slice 8

theorem profileHistogram :
    allCounts.length = 84 ∧ allCounts.all (fun n => decide (5 ≤ n)) = true ∧
    allCounts.count 5 = 3 ∧ allCounts.count 6 = 30 ∧ allCounts.count 7 = 36 ∧
    allCounts.count 8 = 15 := by
  unfold allCounts
  rw [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8]
  decide

end PEqualNP.Outside.L_meta_3360_profile


theorem PEqualNP.Outside.L_meta_3360_profile :
  let edges : List Nat := [1,12,23,34,40,5,16,27,38,57,68,85]
  let target (input : Fin 9 → Bool) : Bool :=
    edges.any fun e => input (Fin.ofNat 9 (e / 10)) && input (Fin.ofNat 9 (e % 10))
  let row (i j k pattern outside : Nat) (v : Fin 9) : Bool :=
    if v.val = i then pattern.testBit 0
    else if v.val = j then pattern.testBit 1
    else if v.val = k then pattern.testBit 2
    else decide (v.val = outside)
  let columns (i j k : Nat) : List Nat :=
    9 :: (List.range 9).filter (fun v => v != i && v != j && v != k)
  let signature (i j k pattern : Nat) : List Bool :=
    (columns i j k).map fun outside => target (row i j k pattern outside)
  let profileCount (i j k : Nat) : Nat :=
    ((List.range 8).map (signature i j k)).eraseDups.length
  let slice (i : Nat) : List Nat :=
    (List.range 9).flatMap fun j =>
      if i < j then ((List.range 9).filter (fun k => decide (j < k))).map (profileCount i j)
      else []
  let allCounts : List Nat :=
    slice 0 ++ slice 1 ++ slice 2 ++ slice 3 ++ slice 4 ++ slice 5 ++ slice 6 ++ slice 7 ++ slice 8
  allCounts.length = 84 ∧ allCounts.all (fun n => decide (5 ≤ n)) = true ∧
      allCounts.count 5 = 3 ∧ allCounts.count 6 = 30 ∧ allCounts.count 7 = 36 ∧
      allCounts.count 8 = 15 := by
  exact PEqualNP.Outside.L_meta_3360_profile.profileHistogram
