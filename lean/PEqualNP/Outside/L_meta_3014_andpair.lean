import Mathlib
import PEqualNP.Outside.L_meta_3014_andand

/-!
# L-meta-3014: the repaired `AndPairClean` is still not a lemma

`PEqualNP.Outside.L_meta_3014_andand` reduces the AND-in-AND case of the negation of
`L-meta-3014` to

  `AndPairClean C`: every **AND** gate of `C` is false at `1_uv` for every non-edge pair `uv`,

the AND-restricted repair (PR #8117) of the first version `AndPairCleanAll`, which quantified
over all gates and was refuted by `exists_correct_not_andPairCleanAll`.

This file settles the status of the repaired form. It is **false as a statement about circuits**,
so it is not a lemma of the argument and cannot be discharged from the other hypotheses:

* `exists_monotone_not_andPairClean` — an explicit one-gate circuit (a single AND gate reading a
  non-edge pair) that is monotone and violates `AndPairClean`. No hypotheses at all: monotonicity
  alone does not give it.
* `exists_correct_not_andPairClean` — the sharp form: from **any** monotone circuit `C` that
  computes `hwFun` on all inputs, appending one dead AND gate over a non-edge pair `{u, v}` gives
  a monotone circuit with the **same** function on every input on which `AndPairClean` fails
  (the appended gate is TRUE at `1_uv`, because both of its inputs are). Correctness does not
  give it either.

What survives as a hypothesis: `AndPairClean` is only ever used on circuits of size at most 26
(`neg_of_andPairClean`), and *no* such circuit computes `hwFun` — which is `L-meta-3014` itself.
So `AndPairClean` restricted to the circuits the argument is about is vacuously true, and every
proof of it is a proof of `L-meta-3014`. It is not a stepping stone.

The smallest corrected statement therefore has to keep the cone condition, which the
counterexample violates: the appended gate does not sit in the cone of the output gate. In
blocking form it reads: if an AND gate is true at `1_uv` for a non-edge pair, then some AND gate
strictly in its cone is false at `1_uv`. This file does not prove that statement; it proves that
the unrestricted form is false, which is what rules out the current route.
-/

namespace PEqualNP.Outside.L_meta_3014_andpair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3014_neg
open PEqualNP.Outside.L_meta_1983
open PEqualNP.Outside.L_meta_3014_andand

/-- The AND gate reading the two wires `u` and `v`. -/
def andGate (u v : Fin 14) : Gate := Gate.mk GateOp.and [u.val, v.val]

lemma andGate_op (u v : Fin 14) : (andGate u v).op = GateOp.and := rfl

lemma andGate_inputs (u v : Fin 14) : (andGate u v).inputs = [u.val, v.val] := rfl

/-- `0` and `1` are not adjacent in the Heawood graph (the neighbours of `0` are `7`, `8`, `10`). -/
lemma not_adj_zero_one : ¬ hw.Adj (0 : Fin 14) (1 : Fin 14) := by
  rw [hw_adj]
  decide +kernel

/-- `Monotone2` survives appending an AND gate of fan-in two. -/
lemma monotone2_append_andGate (C : Circuit) (hM : Monotone2 C) (u v : Fin 14) :
    Monotone2 (Circuit.mk (C.gates ++ [andGate u v]) C.output) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hM g hg
  · refine ⟨by simp [andGate], by simp [andGate]⟩

/-- Wire `z` of the input `1_uv` is true when `z` is `u` or `v`. -/
lemma bitsOf_pair_getD (u v z : Fin 14) (h : z = u ∨ z = v) :
    (List.ofFn (bitsOf ({u, v} : Finset (Fin 14)))).getD (z : ℕ) false = true := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rcases h with rfl | rfl <;> simp [bitsOf]

/-- The wire of the AND gate appended to `C` is TRUE at the input `1_uv`: both of its inputs are
`u` and `v`, and both are true there. -/
lemma getD_append_andGate (C : Circuit) (u v : Fin 14) :
    (wiresFrom (C.gates ++ [andGate u v])
      (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).getD (14 + C.gates.length) false
      = true := by
  rw [wiresFrom_append, wiresFrom_singleton]
  have hlen2 : (wiresFrom C.gates
      (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).length = 14 + C.gates.length := by
    rw [length_wiresFrom]
    simp
  rw [← hlen2, getD_snoc_eq, andGate_op, andGate_inputs]
  simp only [GateOp.eval, List.map_cons, List.map_nil]
  rw [getD_wiresFrom_lt C.gates (List.ofFn (bitsOf ({u, v} : Finset (Fin 14)))) (u : ℕ)
      (by simp), getD_wiresFrom_lt C.gates (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))
      (v : ℕ) (by simp), bitsOf_pair_getD u v u (Or.inl rfl), bitsOf_pair_getD u v v (Or.inr rfl)]
  simp

/-- The wire of the AND gate of the one-gate circuit is TRUE at the input `1_uv`. -/
lemma getD_single_andGate (u v : Fin 14) :
    (wiresFrom [andGate u v]
      (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).getD 14 false = true := by
  simpa using getD_append_andGate (Circuit.mk [] 14) u v

/-- **Monotonicity alone does not give `AndPairClean`.** The circuit with the single AND gate
reading the non-edge pair `{0, 1}` is monotone and its only AND gate is TRUE at `1_01`. -/
theorem exists_monotone_not_andPairClean :
    ∃ C : Circuit, Monotone2 C ∧ ¬ AndPairClean C := by
  refine ⟨Circuit.mk [andGate 0 1] 14, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨by simp [andGate], by simp [andGate]⟩
  · intro h
    have hg : ([andGate 0 1] : List Gate).get ⟨0, by simp⟩ = andGate 0 1 := rfl
    have hop : (([andGate 0 1] : List Gate).get ⟨0, by simp⟩).op = GateOp.and := by
      rw [hg]
      exact andGate_op 0 1
    have hv := h ⟨0, by simp⟩ hop (0 : Fin 14) 1 not_adj_zero_one
    have hv2 : (wiresFrom [andGate 0 1]
        (List.ofFn (bitsOf ({0, 1} : Finset (Fin 14))))).getD 14 false = false := by
      simpa using hv
    rw [getD_single_andGate 0 1] at hv2
    exact absurd hv2 (by simp)

/-- **Correctness does not give `AndPairClean` either.** From any monotone circuit `C` that
computes `hwFun` on every input, appending one dead AND gate over a non-edge pair `{u, v}` gives
a monotone circuit with the same function on every input, on which `AndPairClean` fails: the
appended gate is TRUE at `1_uv`, and it is dead because the output wire is an earlier wire.

The hypothesis `hout` (`C.output < 14 + C.gates.length`, the output wire exists) is what
`eval_append_dead` needs; the cone condition that `AndPairClean` would need — every gate in the
cone of the output gate — is exactly what the appended gate violates. -/
theorem exists_correct_not_andPairClean (C : Circuit) (hM : Monotone2 C)
    (hout : C.output < 14 + C.gates.length)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (u v : Fin 14) (hne : ¬ hw.Adj u v) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hwFun x = true) ∧
      ¬ AndPairClean D := by
  refine ⟨Circuit.mk (C.gates ++ [andGate u v]) C.output,
    monotone2_append_andGate C hM u v, ?_, ?_⟩
  · intro x
    rw [eval_append_dead C (andGate u v) (List.ofFn x) (by simpa using hout)]
    exact hf x
  · intro h
    have hg : (C.gates ++ [andGate u v]).get ⟨C.gates.length, by simp⟩ = andGate u v :=
      get_append_last C.gates (andGate u v) _ rfl
    have hop : ((C.gates ++ [andGate u v]).get ⟨C.gates.length, by simp⟩).op
        = GateOp.and := by
      rw [hg]
      exact andGate_op u v
    have hv := h ⟨C.gates.length, by simp⟩ hop u v hne
    have hv2 : (wiresFrom (C.gates ++ [andGate u v])
        (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).getD (14 + C.gates.length) false
        = false := by
      simpa using hv
    rw [getD_append_andGate C u v] at hv2
    exact absurd hv2 (by simp)

end PEqualNP.Outside.L_meta_3014_andpair
