import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3406_617
    (inputCase : ∀ (pin : Fin 11) (i : ℕ), i < 11 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        (w ++ [!w.getD pin.val false]).getD i false ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (gateCase : ∀ (pin : Fin 11) (D : Circuit), FanInTwo D → 0 < D.size → D.size ≤ 13 →
      D.output = 10 + D.size →
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ a ∈ D.gates[j].inputs, a < 11 + j ∨ a = 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [!w.getD pin.val false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       x2.output ≤ (24 : ℕ) →         (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (24 : ℕ)) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];             x2.eval (x8 ++ [!x8.getD (↑x1) Bool.false]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pin C fan budget _ _
  let input := fun x : Fin 9 → Bool =>
    let w := List.ofFn x ++ [x 0 || x 4]
    w ++ [!w.getD pin.val false]
  have inputLen (x : Fin 9 → Bool) : (input x).length = 11 := by
    simp [input]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldAppend (gs : List Gate) (w : List Bool) :
      ∃ tail, gs.foldl step w = w ++ tail := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨tail, ht⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tail, ?_⟩
      rw [List.foldl_cons, ht]
      simp [step]
  have foldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  by_cases first : C.output < 11
  · obtain ⟨x, hx⟩ := inputCase pin C.output first
    refine ⟨x, ?_⟩
    change ((C.gates.foldl step (input x)).getD C.output false) ≠ _
    obtain ⟨tail, ht⟩ := foldAppend C.gates (input x)
    rw [ht, List.getD_append _ _ _ _ (by simpa [inputLen] using first)]
    exact hx
  by_cases valid : C.output < 11 + C.size
  · let n := C.output - 10
    have npos : 0 < n := by omega
    have ne : C.output = 10 + n := by omega
    have nle : n ≤ C.gates.length := by
      change C.output < 11 + C.gates.length at valid
      omega
    let prefixGates := C.gates.take n
    have plen : prefixGates.length = n := by
      simp [prefixGates, List.length_take, Nat.min_eq_left nle]
    let clip := fun (k : ℕ) (g : Gate) =>
      { g with inputs := g.inputs.map (fun a => if a < k then a else 24) }
    have clipStep (w : List Bool) (g : Gate) (h : w.length ≤ 24) :
        step w (clip w.length g) = step w g := by
      dsimp [step, clip]
      rw [List.map_map]
      apply congrArg (fun values => w ++ [g.op.eval values])
      apply List.map_congr_left
      intro a _
      by_cases ha : a < w.length
      · simp [ha]
      · change w.getD (if a < w.length then a else 24) false = w.getD a false
        rw [if_neg ha, List.getD_eq_default _ _ h,
          List.getD_eq_default _ _ (Nat.le_of_not_gt ha)]
    have clipFold (gs : List Gate) (w : List Bool) (h : w.length + gs.length ≤ 24) :
        (gs.mapIdx (fun j g => clip (w.length + j) g)).foldl step w = gs.foldl step w := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        simp only [List.length_cons] at h
        rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons, Nat.add_zero,
          clipStep _ _ (by omega)]
        simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (step w g) (by simp [step]; omega)
    let D : Circuit := ⟨prefixGates.mapIdx (fun j g => clip (11 + j) g), C.output⟩
    have dsize : D.size = n := by
      change (prefixGates.mapIdx (fun j g => clip (11 + j) g)).length = n
      rw [List.length_mapIdx, plen]
    have dfan : FanInTwo D := by
      intro g hg
      obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
      have hp : j < prefixGates.length := by simpa [D] using hj
      have oldmem : prefixGates[j] ∈ C.gates :=
        (List.take_sublist n C.gates).subset (List.getElem_mem hp)
      obtain ⟨op, arity⟩ := fan _ oldmem
      rw [← hgj]
      simp only [D, List.getElem_mapIdx, clip, List.length_map]
      exact ⟨op, arity⟩
    have dreads : ∀ (j : ℕ) (hj : j < D.gates.length),
        ∀ a ∈ D.gates[j].inputs, a < 11 + j ∨ a = 24 := by
      intro j hj a ha
      simp only [D, List.getElem_mapIdx, clip, List.mem_map] at ha
      obtain ⟨b, _, rfl⟩ := ha
      split <;> simp_all
    have dout : D.output = 10 + D.size := by
      change C.output = 10 + D.size
      rw [dsize]
      exact ne
    obtain ⟨x, hx⟩ := gateCase pin D dfan (by omega) (by omega) dout dreads
    refine ⟨x, ?_⟩
    change (D.eval (input x) ≠ _) at hx
    change (C.eval (input x) ≠ _)
    have same : D.eval (input x) = C.eval (input x) := by
      have clipped := clipFold prefixGates (input x) (by rw [inputLen, plen]; omega)
      rw [inputLen] at clipped
      change ((prefixGates.mapIdx (fun j g => clip (11 + j) g)).foldl step (input x)).getD
        C.output false = (C.gates.foldl step (input x)).getD C.output false
      rw [clipped]
      obtain ⟨tail, ht⟩ := foldAppend (C.gates.drop n) (prefixGates.foldl step (input x))
      have splitGates : prefixGates ++ C.gates.drop n = C.gates := List.take_append_drop _ _
      rw [← splitGates, List.foldl_append, ht]
      exact (List.getD_append _ _ _ _ (by rw [foldLen, inputLen, plen]; omega)).symm
    rwa [same] at hx
  · let x : Fin 9 → Bool := fun i => i == 0 || i == 1
    refine ⟨x, ?_⟩
    change ((C.gates.foldl step (input x)).getD C.output false) ≠ _
    have past : (C.gates.foldl step (input x)).length ≤ C.output := by
      rw [foldLen, inputLen]
      exact Nat.le_of_not_gt valid
    rw [List.getD_eq_default _ _ past]
    decide
