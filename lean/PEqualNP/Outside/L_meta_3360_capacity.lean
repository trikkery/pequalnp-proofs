import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_3360_capacity :
    let Q := ([(50,114),(69,197),(104,105),(104,232),(116,124),(138,394),(201,203),(201,457),(208,216),(261,325),(276,308),(385,401),(402,406)] : List (Fin 512 × Fin 512)).toFinset
    let pool := fun (p : Fin 512) (a : Bool) (n : Fin 512) =>
      if a then decide (n.val &&& p.val = p.val) else decide (n.val &&& p.val ≠ 0)
    ∀ (p : Fin 512) (a : Bool), (Q.filter fun e => pool p a e.1 ≠ pool p a e.2).card ≤ 2 := by decide

