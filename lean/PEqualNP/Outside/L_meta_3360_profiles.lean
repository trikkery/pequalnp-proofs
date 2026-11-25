import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3360_profiles

def row := fun (i j k : Fin 9) (pattern : Fin 8) (outside : Fin 10) (v : Fin 9) =>
      if v = i then (pattern.val + (0 : ℕ)).testBit 0 else if v = j then (pattern.val + (0 : ℕ)).testBit 1
      else if v = k then (pattern.val + (0 : ℕ)).testBit 2 else decide (v.val = outside.val + (0 : ℕ))

def target := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))

def choice (i j k : Fin 9) (p : Fin 5) : Fin 8 :=
  let rows : List (Fin 8) :=
    if (i.val,j.val,k.val) = (0,3,4) ∨ (i.val,j.val,k.val) = (2,5,7) then [0,1,2,3,5]
    else if (i.val,j.val,k.val) = (0,6,8) ∨ (i.val,j.val,k.val) = (2,6,8) then [0,1,2,4,5]
    else if (i.val,j.val,k.val) = (1,6,8) then [0,1,3,4,5]
    else [0,1,2,3,4]
  rows.getD p.val 0

def Slice (i : Fin 9) : Prop :=
  ∀ j k : Fin 9, i < j → j < k → ∀ a b : Fin 5, a ≠ b →
    ∃ t : Fin 10, target (row i j k (choice i j k a) t) ≠ target (row i j k (choice i j k b) t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice0 : Slice 0 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice1 : Slice 1 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice2 : Slice 2 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice3 : Slice 3 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice4 : Slice 4 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice5 : Slice 5 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice6 : Slice 6 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice7 : Slice 7 := by
  unfold Slice
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice8 : Slice 8 := by
  unfold Slice
  decide

theorem profiles : let row := fun (i j k : Fin 9) (pattern : Fin 8) (outside : Fin 10) (v : Fin 9) =>
      if v = i then (pattern.val + (0 : ℕ)).testBit 0 else if v = j then (pattern.val + (0 : ℕ)).testBit 1
      else if v = k then (pattern.val + (0 : ℕ)).testBit 2 else decide (v.val = outside.val + (0 : ℕ))
    let target := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
    ∀ i j k : Fin 9, i < j → j < k → ∃ pat : Fin 5 → Fin 8,
      ∀ a b : Fin 5, a ≠ b → ∃ t : Fin 10,
        target (row i j k (pat a) t) ≠ target (row i j k (pat b) t) := by
  dsimp only
  intro i j k hij hjk
  refine ⟨choice i j k, ?_⟩
  have all (r : Fin 9) : Slice r := by
    fin_cases r <;> first | exact slice0 | exact slice1 | exact slice2 | exact slice3 | exact slice4 | exact slice5 | exact slice6 | exact slice7 | exact slice8
  exact all i j k hij hjk

theorem cannotSummarize (i j k : Fin 9) (hij : i < j) (hjk : j < k)
    (encode : Fin 8 → Fin 4) :
    ∃ a b : Fin 8, encode a = encode b ∧ ∃ t : Fin 10,
      target (row i j k a t) ≠ target (row i j k b t) := by
  obtain ⟨pat, separates⟩ := profiles i j k hij hjk
  obtain ⟨u, v, huv, henc⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun r : Fin 5 => encode (pat r)) (by decide)
  exact ⟨pat u, pat v, henc, separates u v huv⟩

def orOnePattern (p : Fin 6) : Fin 8 :=
  ([1,2,3,5,6,7] : List (Fin 8)).getD p.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sixPatternsWithSameFirstGate :
    ∀ k : Fin 9, k = 6 ∨ k = 8 →
      (∀ p : Fin 6, ∀ t : Fin 10, (row 0 2 k (orOnePattern p) t 0 ||
        row 0 2 k (orOnePattern p) t 2) = true) ∧
      ∀ p q : Fin 6, p ≠ q → ∃ t : Fin 10,
        target (row 0 2 k (orOnePattern p) t) ≠ target (row 0 2 k (orOnePattern q) t) := by
  decide

end PEqualNP.Outside.L_meta_3360_profiles


theorem PEqualNP.Outside.L_meta_3360_profiles :
  let row := fun (i j k : Fin 9) (pattern : Fin 8) (outside : Fin 10) (v : Fin 9) =>
        if v = i then (pattern.val + (0 : ℕ)).testBit 0 else if v = j then (pattern.val + (0 : ℕ)).testBit 1
        else if v = k then (pattern.val + (0 : ℕ)).testBit 2 else decide (v.val = outside.val + (0 : ℕ))
      let target := fun (z : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
          z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
      ∀ i j k : Fin 9, i < j → j < k → ∃ pat : Fin 5 → Fin 8,
        ∀ a b : Fin 5, a ≠ b → ∃ t : Fin 10,
          target (row i j k (pat a) t) ≠ target (row i j k (pat b) t) := by
  exact PEqualNP.Outside.L_meta_3360_profiles.profiles
