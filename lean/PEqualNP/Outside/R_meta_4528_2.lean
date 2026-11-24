import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The step feeds the circuit eleven inputs: the nine variables, then `!x 0` and `x 0 || x x1`.
-- Both extra wires are themselves computed from the variables by one fan-in-two gate each, so
-- every circuit on that eleven-wire input list is a circuit on the nine variables plus two
-- gates. The base bound below is the nine-variable lower bound of sixteen gates; the step's
-- thirteen is exactly that sixteen minus the two gates the extra inputs cost.
theorem PEqualNP.Outside.R_meta_4528_2
    (gadget : ∀ (C : Circuit) (x1 : Fin 9), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 2 ∧
        ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) =
          C.eval (List.ofFn y ++ [!y (0 : Fin 9), y (0 : Fin 9) || y x1]))
    (base : ∀ D : Circuit, FanInTwo D →
      (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) =
        (y (0 : Fin 9) && y (1 : Fin 9) || y (1 : Fin 9) && y (2 : Fin 9) ||
          y (2 : Fin 9) && y (3 : Fin 9) || y (3 : Fin 9) && y (4 : Fin 9) ||
          y (4 : Fin 9) && y (0 : Fin 9) || y (0 : Fin 9) && y (5 : Fin 9) ||
          y (1 : Fin 9) && y (6 : Fin 9) || y (2 : Fin 9) && y (7 : Fin 9) ||
          y (3 : Fin 9) && y (8 : Fin 9) || y (5 : Fin 9) && y (7 : Fin 9) ||
          y (6 : Fin 9) && y (8 : Fin 9) || y (8 : Fin 9) && y (5 : Fin 9))) →
      16 ≤ D.size) :
    ∀ (x1 : Fin (9 : ℕ)), x1 = (1 : Fin (9 : ℕ)) ∨ x1 = (6 : Fin (9 : ℕ)) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x6 ++
            [!x6 (0 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 x1]) ≠
          (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
            x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
            x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
            x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
            x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
            x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
            x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
            x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
            x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
            x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
            x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
            x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 _ C hfan hsize
  by_contra h
  push_neg at h
  obtain ⟨D, hDfan, hDsize, hDeq⟩ := gadget C x1 hfan
  have hb := base D hDfan (fun y => (hDeq y).trans (h y))
  omega
