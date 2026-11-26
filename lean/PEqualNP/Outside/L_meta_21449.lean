import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_21449 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (404 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [2, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  let : DecidableEq GateOp := NestedCover.gateOpDecEq
  unfold Monotone2
  decide
