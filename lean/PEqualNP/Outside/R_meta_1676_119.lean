import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2010
import PEqualNP.Outside.L_meta_2155
import PEqualNP.Outside.R_meta_1676_1
import PEqualNP.Outside.R_meta_1676_118

/-!
Two tighter cuts of `L-meta-1676`. Both reuse merged work instead of assuming it:

* the `gates[1]? = none` branch of `R_meta_1676_1` is discharged by `L_meta_2155`;
* the `structure_or_smaller` hypothesis of `R_meta_1676_118` is discharged by
  `L_meta_2010`.

So the step now rests on three hypotheses in either cut, not four.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.R_meta_1676_119

/-- The edge function of the Petersen graph minus a vertex. -/
def F : (Fin 9 → Bool) → Bool :=
  fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

/-- Cut A: the second gate is an AND, an OR or a NOT. The missing fourth case
(`gates[1]? = none`) is the merged theorem `L_meta_2155`. -/
theorem cut_by_second_op
    (hAnd : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = F → C.gates[1]?.map (fun g => g.op) = some GateOp.and → 16 ≤ C.size)
    (hOr : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = F → C.gates[1]?.map (fun g => g.op) = some GateOp.or → 16 ≤ C.size)
    (hNot : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = F → C.gates[1]?.map (fun g => g.op) = some GateOp.not → 16 ≤ C.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = F → 16 ≤ C.size :=
  PEqualNP.Outside.R_meta_1676_1 hAnd hOr hNot PEqualNP.Outside.L_meta_2155

/-- The edge function as the edge list of the graph, in the shape `R_meta_1676_118`
and `L_meta_2010` use. -/
def G : (Fin 9 → Bool) → Bool :=
  fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

/-- Cut B: the structural cut of `R_meta_1676_118` with its first hypothesis
(`structure_or_smaller`) supplied by `L_meta_2010`. -/
theorem cut_by_structure
    (unrestricted : ¬ HasCircuitSize 9 G 14)
    (theta_lower : ∀ s : ℕ, HasCircuitSize 7 (fun y : Fin 7 → Bool =>
      G ((0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false y))) s → 11 ≤ s)
    (no_three_slices : ¬ (∃ B : Circuit, FanInTwo B ∧ B.size = 11 ∧
      circuitFun 7 B = (fun y : Fin 7 → Bool =>
        G ((0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false y))) ∧
      ∀ t : Bool, ∃ (u v : ℕ) (D : Circuit),
      D.output = B.output + 1 ∧
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun j k => k = j + 1 ∨ k = 0 ∧ (j = u ∨ j = v))
          g.inputs h.inputs) B.gates D.gates ∧
      ∀ y : Fin 7 → Bool, D.eval (true :: List.ofFn y) =
        G ((0 : Fin 9).insertNth t ((3 : Fin 8).insertNth (!t) y)))) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = F → 16 ≤ C.size :=
  PEqualNP.Outside.R_meta_1676_118 PEqualNP.Outside.L_meta_2010
    unrestricted theta_lower no_three_slices

end PEqualNP.Outside.R_meta_1676_119
