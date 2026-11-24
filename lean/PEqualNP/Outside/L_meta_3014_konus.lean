import Mathlib
import PEqualNP.Outside.L_meta_3014_neg

/-!
# L-meta-3014: the cone ("Konus") statement — refuted as stated, true one level up

`PEqualNP.Outside.L_meta_3014_neg` refutes `L-meta-3014` under the hypothesis that no AND gate
lies strictly inside the cone of an AND gate. The repaired AND-in-AND route of the PR series
(`L_meta_3014_andand`) isolates the remaining statement, quoted there verbatim:

> for EVERY AND gate of a correct circuit, that gate is false at `1_uv` for every non-edge `uv`.
> Equivalent blocking form: given an AND gate that is true at some `1_uv` with `uv` a non-edge,
> there is an AND gate strictly in its cone that is false at `1_uv`.

This file settles that statement, and nothing else. `KonusBlocking` is the blocking form written
out in the vocabulary of the repo (`InCone n C a b`: gate `a` lies strictly inside the cone of
gate `b`, that is `b` reads `a` directly or through a chain; in particular `a < b`).

* `exists_correct_not_konusBlocking` — **the statement is false.** Take ANY circuit `C` with an
  output wire, and append one dead AND gate reading the two input wires `u`, `v` of a non-edge
  pair. The new circuit has the same value on every input (`eval_append_dead`) and the same
  monotonicity, but the new AND gate is TRUE at `1_uv`, and its cone is EMPTY: it reads only the
  input wires `u`, `v`, which are not gates. So there is no AND gate in its cone at all, false or
  otherwise. Since the construction preserves monotonicity and the computed function, the
  statement does not follow from the hypotheses of `L-meta-3014`; instantiated at any correct
  circuit it is an outright counterexample, with no hypotheses left.

  The failure is structural, not a detail of the dead gate: the cone of a gate is the set of
  gates BELOW it (what it reads), while truth at `1_uv` can only be blocked ABOVE it. An AND gate
  that is true at `1_uv` says nothing about the AND gates it reads — an AND gate reading the two
  wires of a non-edge pair is the smallest true one, and it has no cone.

* `blocking_above` — **the blocking form is true in the other direction**, and that is the form
  the argument can use: if an AND gate `i` is true at `1_uv` for a non-edge `uv`, `C` is correct,
  and `i` feeds the output (`InCone 14 C i o` for the output gate `o`), then some AND gate `j`
  ABOVE `i` (`InCone 14 C i j`, so `i` lies in the cone of `j`) is false at `1_uv`. The proof is
  the path argument: assume every AND gate above `i` were true at `1_uv`; then by induction on the
  gate index every gate above `i` is true at `1_uv` (an OR gate is true as soon as one of its
  inputs is, and the input on the path from `i` is), so the output is true, contradicting
  correctness at the non-edge pair.

* `KonusBlockingAbove` / `konusBlockingAbove_of_correct` — the same sentence with the cone read
  upwards, as a named hypothesis: every AND gate that is true at a non-edge `1_uv` has a false AND
  gate above it in its fan-out cone. It follows from the hypotheses of `L-meta-3014` plus the cone
  condition of the AND-in-AND route, so it costs nothing and is the form to use.

So the two readings are separated: "false AND gate BELOW the true one" is false, "false AND gate
ABOVE the true one" is true. Nothing here proves `AndPairClean`; the honest remaining hypothesis
is the AND-in-AND case itself, and this file shows the blocking sentence is not it in the
downward reading.
-/

namespace PEqualNP.Outside.L_meta_3014_konus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_3014_neg PEqualNP.Outside.L_meta_1983

attribute [local instance] gateOpDecEq

/-- The edge list of `L_meta_1983` is the edge list of `L_meta_3014_neg`. -/
lemma hwEdges_eq_hL : hwEdges = PEqualNP.Outside.L_meta_1983.hL := rfl

/-- The input `1_uv`: true exactly at `u` and at `v`. -/
abbrev oneUV (u v : Fin 14) : Fin 14 → Bool := bitsOf ({u, v} : Finset (Fin 14))

lemma oneUV_self (u v : Fin 14) : oneUV u v u = true := by
  simp [oneUV, bitsOf]

lemma oneUV_other (u v : Fin 14) : oneUV u v v = true := by
  simp [oneUV, bitsOf]

/-- Gate `j` of `C` is true at the input `1_uv`. -/
def GateTrue (C : Circuit) (j : ℕ) (u v : Fin 14) : Prop :=
  gateVal 14 C j (oneUV u v) = true

/-- Gate `j` of `C` is false at the input `1_uv`. -/
def GateFalse (C : Circuit) (j : ℕ) (u v : Fin 14) : Prop :=
  gateVal 14 C j (oneUV u v) = false

/-- `gateVal` of `EdgeOwnership` is the wire value `V` of `L_meta_1983`. -/
lemma gateVal_eq_V (C : Circuit) (j : ℕ) (u v : Fin 14) :
    gateVal 14 C j (oneUV u v) = V C.gates (List.ofFn (oneUV u v)) (14 + j) := rfl

/-- **The cone statement left open by the AND-in-AND route**, in the vocabulary of the repo:
every AND gate that is true at some `1_uv` with `uv` a non-edge has an AND gate strictly inside
its cone that is false there. `InCone 14 C a b` means that gate `a` lies strictly inside the cone
of gate `b` (gate `b` reads `a`), so the gate whose existence is claimed here is one of the gates
that the true gate reads. -/
def KonusBlocking (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (u v : Fin 14), ¬ hw.Adj u v →
    (gateAt C (i : ℕ)).op = GateOp.and → GateTrue C (i : ℕ) u v →
      ∃ j, InCone 14 C j (i : ℕ) ∧ (gateAt C j).op = GateOp.and ∧ GateFalse C j u v

/-! ### The AND gate over the two wires `u`, `v` -/

/-- The AND gate reading the two input wires `u` and `v`. -/
def andGate (u v : Fin 14) : Gate := Gate.mk GateOp.and [u.val, v.val]

lemma andGate_op (u v : Fin 14) : (andGate u v).op = GateOp.and := rfl

lemma andGate_inputs (u v : Fin 14) : (andGate u v).inputs = [u.val, v.val] := rfl

lemma wiresFrom_singleton (g : Gate) (w : List Bool) :
    wiresFrom [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  simp [wiresFrom]

/-- Appending a gate leaves the value of the output wire alone, as long as the output wire is one
of the wires that were already there. -/
lemma eval_append_dead (C : Circuit) (g : Gate) (x : List Bool)
    (hout : C.output < x.length + C.gates.length) :
    (Circuit.mk (C.gates ++ [g]) C.output).eval x = C.eval x := by
  have h1 : (Circuit.mk (C.gates ++ [g]) C.output).eval x
      = (wiresFrom (C.gates ++ [g]) x).getD C.output false := rfl
  have h2 : C.eval x = (wiresFrom C.gates x).getD C.output false := rfl
  rw [h1, h2, wiresFrom_append, wiresFrom_singleton,
    List.getD_append _ _ _ _ (by rw [length_wiresFrom]; omega)]

/-- `Monotone2` survives appending an AND gate of fan-in two. -/
lemma monotone2_append_andGate (C : Circuit) (hM : Monotone2 C) (u v : Fin 14) :
    Monotone2 (Circuit.mk (C.gates ++ [andGate u v]) C.output) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hM g hg
  · refine ⟨by simp [andGate], by simp [andGate]⟩

/-- A gate appended at the end is the gate at that index. -/
lemma gateAt_append_last (C : Circuit) (g : Gate) :
    gateAt (Circuit.mk (C.gates ++ [g]) C.output) C.gates.length = g := by
  simp [gateAt]

/-- The appended AND gate is true at `1_uv`. -/
lemma andGate_true_at (C : Circuit) (u v : Fin 14) :
    GateTrue (Circuit.mk (C.gates ++ [andGate u v]) C.output) C.gates.length u v := by
  have hbase : (wiresFrom C.gates (List.ofFn (oneUV u v))).length = 14 + C.gates.length := by
    rw [length_wiresFrom]; simp
  have hu : (wiresFrom C.gates (List.ofFn (oneUV u v))).getD (u : ℕ) false = true := by
    rw [getD_wiresFrom_lt _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact oneUV_self u v
  have hv : (wiresFrom C.gates (List.ofFn (oneUV u v))).getD (v : ℕ) false = true := by
    rw [getD_wiresFrom_lt _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact oneUV_other u v
  show (Circuit.wires (Circuit.mk (C.gates ++ [andGate u v]) C.output)
    (List.ofFn (oneUV u v))).getD (14 + C.gates.length) false = true
  show (wiresFrom (C.gates ++ [andGate u v]) (List.ofFn (oneUV u v))).getD
    (14 + C.gates.length) false = true
  rw [wiresFrom_append, wiresFrom_singleton, ← hbase, getD_snoc_eq]
  show (andGate u v).op.eval ((andGate u v).inputs.map fun i =>
    (wiresFrom C.gates (List.ofFn (oneUV u v))).getD i false) = true
  rw [andGate_op, andGate_inputs]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    List.getD_eq_getElem?_getD] at hu hv ⊢
  simp only [hu, hv]
  rfl

/-- **Nothing lies in the cone of the appended AND gate.** It reads only the input wires `u` and
`v`, and input wires are not gates. -/
lemma not_inCone_append (C : Circuit) (u v : Fin 14) (j : ℕ) :
    ¬ InCone 14 (Circuit.mk (C.gates ++ [andGate u v]) C.output) j C.gates.length := by
  intro hc
  have hk : C.gates.length < (C.gates ++ [andGate u v]).length := by simp
  obtain ⟨w, hw, h14, -, -⟩ := (inCone_iff 14 _ j C.gates.length hk).1 hc
  have hgat : (gateAt (Circuit.mk (C.gates ++ [andGate u v]) C.output)
      C.gates.length).inputs = [u.val, v.val] := by
    rw [gateAt_append_last]; exact andGate_inputs u v
  rw [hgat] at hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with hw | hw <;> omega

/-! ### The cone statement is false -/

/-- **The blocking form of the AND-in-AND statement is refuted.** From ANY circuit with an output
wire — correct or not, the construction preserves the computed function — appending one dead AND
gate over a non-edge pair `uv` gives a circuit of the same monotonicity and the same value on
every input, in which that AND gate is TRUE at `1_uv` and no gate at all, hence no false AND gate,
lies in its cone. So `KonusBlocking` is not a consequence of the hypotheses of `L-meta-3014`. -/
theorem exists_correct_not_konusBlocking (C : Circuit) (hM : Monotone2 C)
    (hout : C.output < 14 + C.gates.length)
    (_hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (u v : Fin 14) (hne : ¬ hw.Adj u v) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      ¬ KonusBlocking D := by
  refine ⟨Circuit.mk (C.gates ++ [andGate u v]) C.output,
    monotone2_append_andGate C hM u v, ?_, ?_⟩
  · intro x
    exact eval_append_dead C (andGate u v) (List.ofFn x) (by simpa using hout)
  · intro h
    have hop : (gateAt (Circuit.mk (C.gates ++ [andGate u v]) C.output) C.gates.length).op
        = GateOp.and := by
      rw [gateAt_append_last]; exact andGate_op u v
    have htrue : GateTrue (Circuit.mk (C.gates ++ [andGate u v]) C.output) C.gates.length u v :=
      andGate_true_at C u v
    obtain ⟨j, hcone, -, -⟩ :=
      h ⟨C.gates.length, by simp⟩ u v hne hop htrue
    exact not_inCone_append C u v j hcone

/-- The statement fails for the plain (hypothesis-free) reading as well, as soon as one correct
circuit exists: the hypotheses `hf` above are only there to say that the counterexample is a
circuit of the kind `L-meta-3014` talks about. -/
theorem konusBlocking_false_of_correct (C : Circuit) (hM : Monotone2 C)
    (hout : C.output < 14 + C.gates.length)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (u v : Fin 14) (hne : ¬ hw.Adj u v) :
    ∃ D : Circuit, ¬ KonusBlocking D := by
  obtain ⟨D, -, -, hD⟩ := exists_correct_not_konusBlocking C hM hout hf u v hne
  exact ⟨D, hD⟩

/-! ### The blocking form is true one level up -/

/-- An edge of the Heawood list is an adjacency, in both orders. -/
lemma adj_of_mem {p l : Fin 14} (h : (p.val, l.val) ∈ hwEdges) : hw.Adj p l := by
  rw [hw_adj]
  unfold adjB
  rw [decide_eq_true_eq]
  exact Or.inl (hwEdges_eq_hL ▸ h)

lemma adj_of_mem' {p l : Fin 14} (h : (p.val, l.val) ∈ hwEdges) : hw.Adj l p := by
  rw [hw_adj]
  unfold adjB
  rw [decide_eq_true_eq]
  exact Or.inr (hwEdges_eq_hL ▸ h)

/-- `hwFun` is false at `1_uv` for a non-edge pair: the only pairs inside `{u, v}` are the loop
`uu`, the loop `vv`, and `uv` itself. -/
lemma hwFun_oneUV_false (u v : Fin 14) (hne : ¬ hw.Adj u v) :
    hwFun (oneUV u v) = false := by
  rw [hwFun_bitsOf_false]
  intro p hp l hl hpl
  rw [Finset.mem_insert, Finset.mem_singleton] at hp hl
  rcases hp with rfl | rfl <;> rcases hl with rfl | rfl
  · exact hw_no_loop hpl rfl
  · exact hne (adj_of_mem hpl)
  · exact hne (adj_of_mem' hpl)
  · exact hw_no_loop hpl rfl

/-- **The blocking AND gate sits ABOVE the true one.** Let `C` be monotone, read back, and
correct for the Heawood function, with output gate `o` (output wire `14 + o`). If an AND gate `i`
is true at `1_uv` for a non-edge `uv` and `i` feeds the output, then some AND gate `j` whose cone
contains `i` (`InCone 14 C i j`) is false at `1_uv`.

This is the mirror image of `KonusBlocking` and the form the AND-in-AND argument can use: truth
at a non-edge pair propagates upwards through OR gates, and only an AND gate above the true one
can stop it. -/
theorem blocking_above (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (o : ℕ) (ho : o < C.gates.length) (hout : C.output = 14 + o)
    (i : ℕ) (_hi : i < C.gates.length) (_hopi : (gateAt C i).op = GateOp.and)
    (hcone : InCone 14 C i o)
    (u v : Fin 14) (hne : ¬ hw.Adj u v) (htrue : GateTrue C i u v) :
    ∃ j, InCone 14 C i j ∧ (gateAt C j).op = GateOp.and ∧ GateFalse C j u v := by
  by_contra hcon
  have hcon' : ∀ j, InCone 14 C i j → (gateAt C j).op = GateOp.and →
      V C.gates (List.ofFn (oneUV u v)) (14 + j) = true := by
    intro j hc hop
    rcases hb : gateVal 14 C j (oneUV u v) with - | -
    · exact absurd ⟨j, hc, hop, hb⟩ hcon
    · rw [← gateVal_eq_V]; exact hb
  have hx : (List.ofFn (oneUV u v)).length = 14 := by simp
  have htrueV : V C.gates (List.ofFn (oneUV u v)) (14 + i) = true := by
    rw [← gateVal_eq_V]; exact htrue
  have hall : ∀ j, j < C.gates.length → InCone 14 C i j →
      V C.gates (List.ofFn (oneUV u v)) (14 + j) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hc
      obtain ⟨w, hw, h14, hlt, h3⟩ := (inCone_iff 14 C i j hj).1 hc
      have hg := gate_some C j hj
      have hwval : V C.gates (List.ofFn (oneUV u v)) w = true := by
        have hw' : w = 14 + (w - 14) := by omega
        rw [hw']
        rcases h3 with h3 | h3
        · rw [← h3]; exact htrueV
        · exact ih (w - 14) (by omega) (by omega) h3
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        simpa using (hM (gateAt C j) (List.mem_of_getElem? hg)).1
      rcases hop with hop | hop
      · exact hcon' j hc hop
      · rw [orN C.gates (List.ofFn (oneUV u v)) hx j _ hg (hRB j hj) hop]
        exact ⟨w, hw, hwval⟩
  have houtval : C.eval (List.ofFn (oneUV u v)) = true := by
    have h1 : C.eval (List.ofFn (oneUV u v))
        = V C.gates (List.ofFn (oneUV u v)) C.output := rfl
    rw [h1, hout]
    exact hall o ho hcone
  have hfun := (hf (oneUV u v)).1 houtval
  rw [hwFun_oneUV_false u v hne] at hfun
  exact Bool.false_ne_true hfun

/-- The blocking form with the cone read the other way: the false AND gate is one that DEPENDS on
the true gate (`InCone 14 C i j`, so `i` lies in the cone of `j`). This is the reading under which
the sentence of the PR text is true; `konusBlockingAbove_of_correct` proves it from the hypotheses
of `L-meta-3014` plus the cone condition that every gate feeds the output gate. -/
def KonusBlockingAbove (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (u v : Fin 14), ¬ hw.Adj u v →
    (gateAt C (i : ℕ)).op = GateOp.and → GateTrue C (i : ℕ) u v →
      ∃ j, InCone 14 C i j ∧ (gateAt C j).op = GateOp.and ∧ GateFalse C j u v

/-- **The blocking form with the cone read upwards holds.** With the hypotheses of
`L-meta-3014` (monotone, reads back, correct) and the cone condition of the AND-in-AND route
(every gate feeds the output gate `o`), every AND gate that is true at a non-edge `1_uv` has a
false AND gate above it in its fan-out cone. Contrast `exists_correct_not_konusBlocking`: no such
gate need lie BELOW it. -/
theorem konusBlockingAbove_of_correct (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (o : ℕ) (ho : o < C.gates.length) (hout : C.output = 14 + o)
    (hcone : ∀ j, j < C.gates.length → InCone 14 C j o) :
    KonusBlockingAbove C := by
  intro i u v hne hop htrue
  exact blocking_above C hM hRB hf o ho hout (i : ℕ) i.2 hop (hcone (i : ℕ) i.2) u v hne htrue

end PEqualNP.Outside.L_meta_3014_konus
