import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3360_nine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 3]⟩,
    ⟨.or, [3, 5]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [13, 10]⟩, ⟨.and, [14, 11]⟩, ⟨.or, [15, 16]⟩], 17⟩

def observed : Finset ℕ := {1, 6, 8, 9, 12, 17}

def edge (x : Fin 9 → Bool) : Bool :=
  ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

def decode (w : List Bool) : Bool :=
  (w.getD 1 false && (w.getD 9 false || w.getD 6 false)) ||
  (w.getD 8 false && (w.getD 12 false || w.getD 6 false)) ||
  (w.getD 17 false && (w.getD 9 false || w.getD 12 false))

theorem rows : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    let w := circuit.wires [b0,b1,b2,b3,b4,b5,b6,b7,b8]
    w.getD 9 false = (b0 || b2) ∧
    decode w = edge ![b0,b1,b2,b3,b4,b5,b6,b7,b8] := by
  decide +kernel

theorem evalRows (x : Fin 9 → Bool) :
    let w := circuit.wires (List.ofFn x)
    w.getD 9 false = (x 0 || x 2) ∧ decode w = edge x := by
  have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] := by
    simp [List.ofFn_succ]
  dsimp only
  rw [hx]
  exact rows (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

theorem sizeAndBasis :
    circuit.size = 9 ∧ FanInTwo circuit ∧ ∀ g ∈ circuit.gates, g.op ≠ .not := by
  refine ⟨rfl, ?_, ?_⟩ <;> intro g hg <;>
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sufficient (x y : Fin 9 → Bool)
    (same : ∀ i ∈ observed,
      (circuit.wires (List.ofFn x)).getD i false =
      (circuit.wires (List.ofFn y)).getD i false) : edge x = edge y := by
  rw [← (evalRows x).2, ← (evalRows y).2]
  simp only [decode, same 1 (by decide), same 6 (by decide), same 8 (by decide),
    same 9 (by decide), same 12 (by decide), same 17 (by decide)]

end PEqualNP.Outside.L_meta_3360_nine

theorem PEqualNP.Outside.L_meta_3360_nine :
    let f : (Fin 9 → Bool) → Bool := fun x =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 9 ∧
      (∀ g ∈ C.gates, g.op ≠ .not) ∧
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) ∧
      ∃ s ⊆ Finset.range 18, s.card = 6 ∧
      ∀ x y : Fin 9 → Bool, (∀ i ∈ s, (C.wires (List.ofFn x)).getD i false =
        (C.wires (List.ofFn y)).getD i false) →
        f x = f y :=
  ⟨PEqualNP.Outside.L_meta_3360_nine.circuit, PEqualNP.Outside.L_meta_3360_nine.sizeAndBasis.2.1, PEqualNP.Outside.L_meta_3360_nine.sizeAndBasis.1,
    PEqualNP.Outside.L_meta_3360_nine.sizeAndBasis.2.2, fun x => (PEqualNP.Outside.L_meta_3360_nine.evalRows x).1,
    PEqualNP.Outside.L_meta_3360_nine.observed, by decide, by decide, PEqualNP.Outside.L_meta_3360_nine.sufficient⟩
