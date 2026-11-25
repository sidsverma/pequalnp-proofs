import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def threshold16 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [14, 4]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [14, 4]⟩, ⟨.and, [17, 5]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 5]⟩, ⟨.and, [20, 6]⟩, ⟨.or, [19, 21]⟩], 22⟩

theorem threshold16_legal : ∀ g ∈ threshold16.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [threshold16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threshold16_correct : ∀ x : Fin 7 → Bool, threshold16.eval (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem threshold16_size : threshold16.gates.length = 16 := rfl

theorem replacement_without_not (n : Nat) (f : (Fin n → Bool) → Bool)
    (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (none : ∀ g ∈ gates, g.op ≠ GateOp.not)
    (correct : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = f x) :
    ∃ (gates' : List Gate) (out' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin n → Bool, Circuit.eval ⟨gates', out'⟩ (List.ofFn x) = f x := by
  refine ⟨gates, out, ?_, le_rfl, correct⟩
  intro g hg
  exact ⟨(legal g hg).1.imp_right (fun h => h.resolve_right (none g hg)), (legal g hg).2⟩

theorem threshold16_replaces_large (gates : List Gate) (hlarge : 16 ≤ gates.length) :
    ∃ (gates' : List Gate) (out : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', out⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact ⟨threshold16.gates, threshold16.output, threshold16_legal, hlarge, threshold16_correct⟩
