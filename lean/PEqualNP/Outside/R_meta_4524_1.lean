import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The two cases a NOT gate can fall into: it reads only input wires, or it reads at least one
gate output. Neither case can happen, so no NOT gate can happen. -/
theorem PEqualNP.Outside.R_meta_4524_1
    (hInput : ∀ (c : Circuit), FanInTwo c → c.size = (13 : ℕ) →
      (∀ (x4 : Fin (8 : ℕ) → Bool), c.eval (List.ofFn x4) = ((fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)))) x4) →
      ∀ g ∈ c.gates, g.op = GateOp.not → (∀ w ∈ g.inputs, w < (8 : ℕ)) → False)
    (hGate : ∀ (c : Circuit), FanInTwo c → c.size = (13 : ℕ) →
      (∀ (x4 : Fin (8 : ℕ) → Bool), c.eval (List.ofFn x4) = ((fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)))) x4) →
      ∀ g ∈ c.gates, g.op = GateOp.not → (∃ w ∈ g.inputs, (8 : ℕ) ≤ w) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (13 : ℕ) → (∀ (x4 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) x4) → ∀ x5 ∈ x1.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro x1 hFan hSize hEval x5 hx5 hop
  by_cases hcase : ∃ w ∈ x5.inputs, (8 : ℕ) ≤ w
  · exact hGate x1 hFan hSize hEval x5 hx5 hop hcase
  · push Not at hcase
    exact hInput x1 hFan hSize hEval x5 hx5 hop hcase
