import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3360_835
    (profiles : let row := fun (i j k : Fin 9) (pattern : Fin 8) (outside : Fin 10) (v : Fin 9) =>
      if v = i then (pattern.val + (0 : ℕ)).testBit 0 else if v = j then (pattern.val + (0 : ℕ)).testBit 1
      else if v = k then (pattern.val + (0 : ℕ)).testBit 2 else decide (v.val = outside.val + (0 : ℕ))
    let target := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
    ∀ i j k : Fin 9, i < j → j < k → ∃ pat : Fin 5 → Fin 8,
      ∀ a b : Fin 5, a ≠ b → ∃ t : Fin 10,
        target (row i j k (pat a) t) ≠ target (row i j k (pat b) t))
    (residual : let row := fun (i j k : Fin 9) (pattern : Fin 8) (outside : Fin 10) (v : Fin 9) =>
      if v = i then (pattern.val + (0 : ℕ)).testBit 0 else if v = j then (pattern.val + (0 : ℕ)).testBit 1
      else if v = k then (pattern.val + (0 : ℕ)).testBit 2 else decide (v.val = outside.val + (0 : ℕ))
    let target := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      C.size = 8 → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      let obs := fun (z : Fin 9 → Bool) (w : ℕ) => (C.wires (List.ofFn z)).getD w false
      (∀ z, obs z 9 = (z 0 || z 2)) →
      ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
      (∀ i j k : Fin 9, i < j → j < k → ∃ pat : Fin 5 → Fin 8,
        ∀ a b : Fin 5, a ≠ b → ∃ t : Fin 10, ∃ w ∈ S,
          obs (row i j k (pat a) t) w ≠ obs (row i j k (pat b) t) w) →
      ∃ x y, target x ≠ target y ∧ ∀ w ∈ S, obs x w = obs y w) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  classical
  dsimp only at profiles residual ⊢
  intro C fan sz mono head S rangeS cardS
  by_contra noCollision
  apply noCollision
  apply residual C fan sz mono head S rangeS cardS
  intro i j k hij hjk
  obtain ⟨pat, hpat⟩ := profiles i j k hij hjk
  refine ⟨pat, ?_⟩
  intro a b hab
  obtain ⟨t, ht⟩ := hpat a b hab
  refine ⟨t, ?_⟩
  by_contra noWire
  push_neg at noWire
  exact noCollision ⟨_, _, ht, noWire⟩

