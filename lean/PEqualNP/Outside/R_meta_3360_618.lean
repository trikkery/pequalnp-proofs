import PEqualNP.Defs

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3360_618
    (capacity : let Q := ([(50,114),(69,197),(104,105),(104,232),(116,124),(138,394),(201,203),(201,457),(208,216),(261,325),(276,308),(385,401),(402,406)] : List (Fin 512 × Fin 512)).toFinset
    let pool := fun (p : Fin 512) (a : Bool) (n : Fin 512) =>
      if a then decide (n.val &&& p.val = p.val) else decide (n.val &&& p.val ≠ 0)
    ∀ (p : Fin 512) (a : Bool), (Q.filter fun e => pool p a e.1 ≠ pool p a e.2).card ≤ 2)
    (mixed : let f := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size = 8 → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ z : Fin 9 → Bool, (C.wires (List.ofFn z)).getD 9 false = (z 0 || z 2)) →
      ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
      (∃ w ∈ S, ∀ (p : Fin 512) (a : Bool), ∃ n : Fin 512,
        (C.wires (List.ofFn (fun v : Fin 9 => n.val.testBit v.val))).getD w false ≠
          (if a then decide (n.val &&& p.val = p.val) else decide (n.val &&& p.val ≠ 0))) →
      ∃ x y, f x ≠ f y ∧ ∀ w ∈ S, (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false) :
    let f := fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size = 8 → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ z : Fin 9 → Bool, (C.wires (List.ofFn z)).getD 9 false = (z 0 || z 2)) →
      ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
      ∃ x y, f x ≠ f y ∧ ∀ w ∈ S, (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  intro C fan sz mono head S rangeS cardS
  classical
  by_contra noCollision
  apply noCollision
  apply mixed C fan sz mono head S rangeS cardS
  by_contra noMixed
  push_neg at noMixed
  let Q := ([(50,114),(69,197),(104,105),(104,232),(116,124),(138,394),(201,203),(201,457),(208,216),(261,325),(276,308),(385,401),(402,406)] : List (Fin 512 × Fin 512)).toFinset
  let pool := fun (p : Fin 512) (a : Bool) (n : Fin 512) =>
      if a then decide (n.val &&& p.val = p.val) else decide (n.val &&& p.val ≠ 0)
  let input := fun (n : Fin 512) (v : Fin 9) => n.val.testBit v.val
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
  have sizeQ : Q.card = 13 := by decide
  have labelled : ∀ e ∈ Q, (fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))) (input e.1) ≠ (fun (z : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        z (Fin.ofNat 9 (e/10)) && z (Fin.ofNat 9 (e%10))) (input e.2) := by decide
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

