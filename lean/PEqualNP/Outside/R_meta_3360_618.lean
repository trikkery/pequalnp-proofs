import PEqualNP.Defs

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3360_618
    (capacity : let Q := ([(50,114),(69,197),(104,105),(104,232),(116,124),(138,394),(201,203),(201,457),(208,216),(261,325),(276,308),(385,401),(402,406)] : List (Fin 512 × Fin 512)).toFinset
    let pool := fun (p : Fin 512) (a : Bool) (n : Fin 512) =>
      if a then decide (Nat.land (n.val + (0 : ℕ)) p.val = p.val) else decide (Nat.land (n.val + (0 : ℕ)) p.val ≠ 0)
    ∀ (p : Fin 512) (a : Bool), (Q.filter fun e => pool p a e.1 ≠ pool p a e.2).card ≤ 2)
    (mixed :
      let f := fun (z : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10));
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size = 8 → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ z : Fin 9 → Bool, (C.wires (List.ofFn z)).getD 9 false = (z 0 || z 2)) →
      ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
      (∃ w ∈ S, ∀ (p : Fin 512) (a : Bool), ∃ n : Fin 512,
        (C.wires (List.ofFn (fun v : Fin 9 => Nat.testBit (n.val + (0 : ℕ)) v.val))).getD w false ≠
          (if a then decide (Nat.land (n.val + (0 : ℕ)) p.val = p.val) else decide (Nat.land (n.val + (0 : ℕ)) p.val ≠ 0))) →
      ∃ x y, f x ≠ f y ∧ ∀ w ∈ S, (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  dsimp only at capacity mixed ⊢
  intro C fan sz mono head S rangeS cardS
  classical
  by_contra noCollision
  apply noCollision
  apply mixed C fan sz mono head S rangeS cardS
  by_contra noMixed
  push_neg at noMixed
  let Q := ([(50,114),(69,197),(104,105),(104,232),(116,124),(138,394),(201,203),(201,457),(208,216),(261,325),(276,308),(385,401),(402,406)] : List (Fin 512 × Fin 512)).toFinset
  let pool := fun (p : Fin 512) (a : Bool) (n : Fin 512) =>
      if a then decide (Nat.land (n.val + (0 : ℕ)) p.val = p.val) else decide (Nat.land (n.val + (0 : ℕ)) p.val ≠ 0)
  let input := fun (n : Fin 512) (v : Fin 9) => Nat.testBit (n.val + (0 : ℕ)) v.val
  let obs := fun (w : ℕ) (n : Fin 512) => (C.wires (List.ofFn (input n))).getD w false
  let seen := fun w => Q.filter fun e => obs w e.1 ≠ obs w e.2
  have bound : ∀ w ∈ S, (seen w).card ≤ 2 := by
    intro w hw
    obtain ⟨p, a, same⟩ := noMixed w hw
    have eqSets : seen w = Q.filter (fun e => pool p a e.1 ≠ pool p a e.2) := by
      ext e
      simp only [seen, Finset.mem_filter]
      have l : obs w e.1 = pool p a e.1 := same e.1
      have r : obs w e.2 = pool p a e.2 := same e.2
      rw [l, r]
    rw [eqSets]
    exact capacity p a
  have sizeQ : Q.card = 13 := by
    dsimp only [Q]
    decide
  have labelled : ∀ e ∈ Q, (fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))) (input e.1) ≠ (fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))) (input e.2) := by
    intro e he
    simp only [Q, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [input] <;> decide
  have small : (S.biUnion seen).card ≤ 12 := calc
    _ ≤ ∑ w ∈ S, (seen w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ S, 2 := Finset.sum_le_sum bound
    _ ≤ 12 := by simpa using (show S.card * 2 ≤ 12 by omega)
  have missing : ∃ e ∈ Q, e ∉ S.biUnion seen := by
    by_contra! full
    have h := Finset.card_le_card (show Q ⊆ S.biUnion seen from full)
    omega
  obtain ⟨e, he, missed⟩ := missing
  apply noCollision
  refine ⟨input e.1, input e.2, labelled e he, ?_⟩
  intro w hw
  by_contra neq
  exact missed (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨he, neq⟩⟩)

