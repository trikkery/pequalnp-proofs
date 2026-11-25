import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5519

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [2, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 1]⟩], 12⟩

end PEqualNP.Outside.L_meta_5519

theorem PEqualNP.Outside.L_meta_5519 :
    PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit).size = 5 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (14335 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  change PEqualNP.MetaComplexity.Monotone2 PEqualNP.Outside.L_meta_5519.witness ∧ _
  refine ⟨?_, rfl, by decide⟩
  intro g hg
  simp [PEqualNP.Outside.L_meta_5519.witness] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp
