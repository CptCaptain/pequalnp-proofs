import Mathlib
import PEqualNP.Outside.L_meta_3014_neg

/-!
# L-meta-3014: the AND-in-AND case

`PEqualNP.Outside.L_meta_3014_neg` refutes `L-meta-3014` under the hypothesis that no AND gate
lies in the cone of an AND gate (`neg_of_noAndAndInCone`). This file isolates the remaining
piece.

The counting core is `pairCleanBound` of `PEqualNP.Outside.L_meta_1602`: a monotone circuit of
fan-in at most two computing the edge function of a graph without 4-cycles has
`edges + cover ≤ gates + 1`, provided every AND gate is FALSE on the three kinds of SMALL inputs
where the edge function is false: the all-false input, a singleton, and a non-edge pair. Call that
condition `AndGateClean`.

* `hwFun_iff_adj`: the bridge from the truth of `hwFun` to an edge of `hw`.
* `andGateClean_of_pairClean`: the singleton and empty cases of `AndGateClean` follow from
  monotonicity alone, so only the NON-EDGE PAIR case is ever missing.
* `andGateClean_of_noAndAnd`: `AndGateClean` holds when no AND gate sits in the cone of an AND
  gate and every gate sits in the cone of the output, so nothing of `L_meta_3014_neg` is lost.
* `size_bound_of_andGateClean`: `AndGateClean` alone gives `27 ≤ C.size`.
* `neg_of_andGateClean`: with `AndGateClean` the whole negation of `L-meta-3014` follows.

## The definition of `AndPairClean` had to be restricted to AND gates

The first version of this file quantified `AndPairClean` over **all** gates, while every use of it
was at a gate with `(C.gates.get i).op = GateOp.and`. In that form the statement is false for the
circuits it is about: an OR gate reading a non-edge pair `{u, v}` is TRUE at `1_uv`, and a circuit
can carry such a gate without changing its function (a dead gate, or a gate whose value an AND
above it masks). `exists_correct_not_andPairCleanAll` makes this precise: from ANY circuit `C`
with an output wire, appending one dead OR gate over a non-edge pair gives a circuit with the same
value on every input and the same monotonicity, whose old-style `AndPairCleanAll` fails. The
repaired `AndPairClean` is AND-restricted, is implied by the old form
(`andPairClean_of_andPairCleanAll`) and is stable under exactly that construction
(`andPairClean_append_orGate`), so it is the strongest form the argument can honestly use.

WHAT IS STILL OPEN (the AND-in-AND case). Even repaired, `AndPairClean` is not a consequence of
the hypotheses of `L-meta-3014` alone, and nothing here proves it: an AND gate may be true on a
non-edge pair as long as an AND gate above it blocks the propagation to the output, and such a
blocking gate is exactly an AND gate in the cone of an AND gate. The smallest remaining statement
is therefore exactly `AndPairClean` itself (`andGateClean_of_pairClean` shows it suffices): for
EVERY AND gate of a correct circuit, that gate is false at `1_uv` for every non-edge `uv`.
Equivalent blocking form: given an AND gate that is true at some `1_uv` with `uv` a non-edge,
there is an AND gate strictly in its cone that is false at `1_uv`, so a top-form normalisation (or
a direct counting argument for circuits with an AND-in-AND pair) is still missing.
-/

namespace PEqualNP.Outside.L_meta_3014_andand

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3014_neg
open PEqualNP.Outside.L_meta_1983

attribute [local instance] gateOpDecEq

instance : DecidableRel hw.Adj := fun u v => decidable_of_iff _ (hw_adj u v).symm

/-- The edge list of `L_meta_1983` is the edge list of `L_meta_3014_neg`. -/
lemma hwEdges_eq_hL : hwEdges = PEqualNP.Outside.L_meta_1983.hL := rfl

/-- `hwFun` is true exactly on the inputs that contain an edge of `hw`. -/
lemma hwFun_iff_adj (x : Fin 14 → Bool) :
    hwFun x = true ↔ ∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true := by
  rw [hwFun_iff, hwEdges_eq_hL]
  exact edge_iff x

/-- The three kinds of input on which the edge function of a graph is false: the all-false input,
a singleton, and a non-edge pair. -/
def SmallInput (x : Fin 14 → Bool) : Prop :=
  x = bitsOf ∅ ∨ (∃ u : Fin 14, x = bitsOf {u}) ∨ (∃ u v : Fin 14, x = bitsOf {u, v})

/-- Every AND gate is false on every small input that is not an edge: the hypothesis the counting
of `PEqualNP.Outside.L_meta_1602` needs. -/
def AndGateClean (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (x : Fin 14 → Bool), SmallInput x →
    (C.gates.get i).op = GateOp.and →
    (wiresFrom C.gates (List.ofFn x)).getD (14 + (i : ℕ)) false = true →
      ∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true

/-- The part of `AndGateClean` that is not free: an AND gate is false at every non-edge pair
(the pair may be a loop, which is never an edge). -/
def AndPairClean (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length), (C.gates.get i).op = GateOp.and →
    ∀ (u v : Fin 14), ¬ hw.Adj u v →
      (wiresFrom C.gates (List.ofFn (bitsOf {u, v}))).getD (14 + (i : ℕ)) false = false

/-- The form of `AndPairClean` used before the repair: it quantifies over **all** gates, so it
claims that every gate — OR gates included — is false at every non-edge pair. That is false for
any circuit that has an OR gate reading a non-edge pair, see
`exists_correct_not_andPairCleanAll`. `AndPairClean` is the AND-restricted form, and it is all
`andGateClean_of_pairClean` ever needs. -/
def AndPairCleanAll (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (u v : Fin 14), ¬ hw.Adj u v →
    (wiresFrom C.gates (List.ofFn (bitsOf {u, v}))).getD (14 + (i : ℕ)) false = false

/-- The OR gate reading the two wires `u` and `v`. -/
def orGate (u v : Fin 14) : Gate := Gate.mk GateOp.or [u.val, v.val]

lemma wiresFrom_singleton (g : Gate) (w : List Bool) :
    wiresFrom [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  simp [wiresFrom]

lemma bitsOf_pair_self (u v : Fin 14) :
    (List.ofFn (bitsOf ({u, v} : Finset (Fin 14)))).getD (u : ℕ) false = true := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp [bitsOf]

/-- The repaired form is implied by the old one. -/
lemma andPairClean_of_andPairCleanAll (C : Circuit) (h : AndPairCleanAll C) :
    AndPairClean C := by
  intro i _ u v hne
  exact h i u v hne

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

lemma get_append_last {α : Type} (l : List α) (a : α) (i : Fin (l ++ [a]).length)
    (h : i.val = l.length) : (l ++ [a]).get i = a := by
  have h2 : i = ⟨l.length, by simp⟩ := Fin.ext h
  subst h2
  simp

lemma get_append_left {α : Type} (l₁ l₂ : List α) (i : Fin (l₁ ++ l₂).length)
    (h : i.val < l₁.length) : (l₁ ++ l₂).get i = l₁.get ⟨i.val, h⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left h

/-- The repaired `AndPairClean` is stable under appending an OR gate: the new gate is not an AND
gate, and it cannot change the wires of the AND gates before it. So the repair removes exactly the
over-strength, and nothing else. -/
lemma andPairClean_append_orGate (C : Circuit) (u v : Fin 14) (h : AndPairClean C) :
    AndPairClean (Circuit.mk (C.gates ++ [orGate u v]) C.output) := by
  intro i hopi u' v' hne
  have hi : (i : ℕ) < C.gates.length := by
    have h1 := i.2
    simp only [List.length_append, List.length_singleton] at h1
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h2 | h2
    · exact h2
    · exfalso
      have hg : (C.gates ++ [orGate u v]).get i = orGate u v := get_append_last C.gates _ i h2
      rw [hg] at hopi
      exact absurd hopi (by simp [orGate])
  have hget : (C.gates ++ [orGate u v]).get i = C.gates.get ⟨i, hi⟩ :=
    get_append_left C.gates _ i hi
  have hwi : (wiresFrom (C.gates ++ [orGate u v])
      (List.ofFn (bitsOf ({u', v'} : Finset (Fin 14))))).getD (14 + (i : ℕ)) false
      = (wiresFrom C.gates (List.ofFn (bitsOf ({u', v'} : Finset (Fin 14))))).getD
        (14 + (i : ℕ)) false := by
    rw [wiresFrom_append, wiresFrom_singleton,
      List.getD_append _ _ _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hopi' : (C.gates.get ⟨i, hi⟩).op = GateOp.and := by
    rw [← hget]
    exact hopi
  rw [hwi]
  exact h ⟨i, hi⟩ hopi' u' v' hne

/-- `Monotone2` survives appending an OR gate of fan-in two. -/
lemma monotone2_append_orGate (C : Circuit) (hM : Monotone2 C) (u v : Fin 14) :
    Monotone2 (Circuit.mk (C.gates ++ [orGate u v]) C.output) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hM g hg
  · refine ⟨by simp [orGate], by simp [orGate]⟩

/-- **The old definition is refuted by the circuits it is meant to talk about.** Take any circuit
`C` with an output wire, and append one dead OR gate reading a non-edge pair `{u, v}`. The new
circuit has the same value on every input (`eval_append_dead`), and the same monotonicity, but the
old `AndPairCleanAll` is false on it: that OR gate is TRUE at `1_uv`. Hence `AndPairCleanAll`
does not follow from the hypotheses of `L-meta-3014`, and the repaired `AndPairClean`
(`andPairClean_append_orGate`) is the strongest form that survives. -/
theorem exists_correct_not_andPairCleanAll (C : Circuit) (hM : Monotone2 C)
    (hout : C.output < 14 + C.gates.length) (u v : Fin 14) (hne : ¬ hw.Adj u v) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      ¬ AndPairCleanAll D := by
  refine ⟨Circuit.mk (C.gates ++ [orGate u v]) C.output,
    monotone2_append_orGate C hM u v, ?_, ?_⟩
  · intro x
    exact eval_append_dead C (orGate u v) (List.ofFn x) (by simpa using hout)
  · intro h
    have hv := h ⟨C.gates.length, by simp⟩ u v hne
    have hw : (wiresFrom (C.gates ++ [orGate u v])
        (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).getD (14 + C.gates.length) false
        = true := by
      rw [wiresFrom_append, wiresFrom_singleton]
      have hlen2 : (wiresFrom C.gates (List.ofFn (bitsOf ({u, v} : Finset (Fin 14))))).length
          = 14 + C.gates.length := by
        rw [length_wiresFrom]
        simp
      rw [← hlen2, getD_snoc_eq]
      have hor : (orGate u v).op = GateOp.or := rfl
      have hin : (orGate u v).inputs = [u.val, v.val] := rfl
      rw [hor, hin]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [getD_wiresFrom_lt C.gates (List.ofFn (bitsOf ({u, v} : Finset (Fin 14)))) (u : ℕ)
          (by simp), bitsOf_pair_self u v]
      simp
    rw [hw] at hv
    exact absurd hv (by simp)

/-- The singleton and empty cases of `AndGateClean` are free: only non-edge pairs are missing. -/
theorem andGateClean_of_pairClean (C : Circuit) (hM : Monotone2 C) (hpair : AndPairClean C) :
    AndGateClean C := by
  intro i x hx hopi hv
  have hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have hloop : ∀ u : Fin 14, ¬ hw.Adj u u := by
    intro u h
    rw [hw_adj] at h
    unfold adjB at h
    rw [decide_eq_true_eq] at h
    rcases h with h | h
    · exact hw_no_loop h rfl
    · exact hw_no_loop h rfl
  rcases hx with h0 | ⟨u, hu⟩ | ⟨u, v, huv⟩
  · -- the all-false input: monotonicity to the loop `00`
    subst h0
    have hle : ∀ j, (List.ofFn (bitsOf (∅ : Finset (Fin 14)))).getD j false = true →
        (List.ofFn (bitsOf ({(0 : Fin 14), 0} : Finset (Fin 14)))).getD j false = true := by
      intro j hj
      by_cases hj' : j < 14
      · rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_ofFn] at hj
        simp [bitsOf] at hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact absurd hj Bool.false_ne_true
    have h2 := wiresFrom_mono C.gates hmono _ _ (by simp) hle (14 + (i : ℕ)) hv
    have h3 := hpair i hopi (0 : Fin 14) 0 (hloop 0)
    rw [h3] at h2
    exact absurd h2 (by simp)
  · -- a singleton is the loop `uu`
    subst hu
    have h3 := hpair i hopi u u (hloop u)
    rw [show ({u, u} : Finset (Fin 14)) = {u} from by simp] at h3
    rw [h3] at hv
    exact absurd hv (by simp)
  · -- a pair: an edge gives the claim, a non-edge contradicts the hypothesis
    subst huv
    by_cases hadj : hw.Adj u v
    · exact ⟨u, v, hadj, by simp [bitsOf], by simp [bitsOf]⟩
    · have h3 := hpair i hopi u v hadj
      rw [h3] at hv
      exact absurd hv (by simp)

/-- Under the hypothesis of `L_meta_3014_neg` (no AND gate in the cone of an AND gate), together
with the cone condition that every gate sits in the cone of the output gate, every AND gate is
false on every non-edge pair: the AND-in-AND case is the only obstruction to `AndGateClean`. -/
theorem andGateClean_of_noAndAnd (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hno : ¬∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 14 C i j)
    (o : ℕ) (ho : o < C.gates.length) (hout : C.output = 14 + o)
    (hcone : ∀ j, j < C.gates.length → InCone 14 C j o)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true) :
    AndGateClean C := by
  intro i x _ hopi hv
  have hlen : (List.ofFn x).length = 14 := by simp
  have hv' : V C.gates (List.ofFn x) (14 + (i : ℕ)) = true := hv
  have hopi' : (gateAt C (i : ℕ)).op = GateOp.and := by
    rw [gateAt_eq C (i : ℕ) i.2]
    exact hopi
  have hgate := up_true C hM hRB hno (List.ofFn x) hlen (i : ℕ) hopi' hv' o ho (hcone i i.2)
  have hev : C.eval (List.ofFn x) = true := by
    rw [show C.eval (List.ofFn x) = V C.gates (List.ofFn x) C.output from rfl, hout, hgate]
  exact (hwFun_iff_adj x).1 ((hf x).1 hev)

/-- `AndGateClean` gives the counting bound `27 ≤ C.size` for the Heawood graph. -/
theorem size_bound_of_andGateClean (C : Circuit) (hM : Monotone2 C)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)
    (hclean : AndGateClean C) : 27 ≤ C.size := by
  have hop : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hM g hg
    refine ⟨?_, h.2⟩
    have h1 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := h.1
    simpa using h1
  have hev : ∀ x : Fin 14 → Bool,
      Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff]
    exact (hf x).trans (hwFun_iff_adj x)
  have hclean' : ∀ (i : Fin C.gates.length) (x : Fin 14 → Bool),
      (x = (fun _ => false) ∨ (∃ u : Fin 14, x = fun z => decide (z = u)) ∨
        (∃ u v : Fin 14, x = fun z => decide (z = u ∨ z = v))) →
      (C.gates.get i).op = GateOp.and →
      (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (14 + (i : ℕ)) false = true →
        ∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hx hopi hv
    refine hclean i x ?_ hopi hv
    rcases hx with h | ⟨u, h⟩ | ⟨u, v, h⟩
    · refine Or.inl ?_
      rw [h]
      funext z
      simp [bitsOf]
    · refine Or.inr (Or.inl ⟨u, ?_⟩)
      rw [h]
      funext z
      simp [bitsOf]
    · refine Or.inr (Or.inr ⟨u, v, ?_⟩)
      rw [h]
      funext z
      simp [bitsOf]
  obtain ⟨T, hT, hcard⟩ :=
    @pairCleanBound 14 hw
      (fun u v => decidable_of_iff _ (hw_adj u v).symm) hw_c4 C.gates C.output hop hev hclean'
  have h7 := cover7 T hT
  have h28 := le_trans (Nat.add_le_add (hw_edges _) h7) hcard
  show 27 ≤ C.gates.length
  omega

/-- The negation of `L-meta-3014` follows from `AndGateClean`. -/
theorem neg_of_andGateClean : NegTarget AndGateClean := by
  rintro ⟨C, hAO2, -, -, h26, hmin, hmax, hcl⟩
  have hM : Monotone2 C := isAO2_monotone2 hAO2
  have hf := eval_iff_hw hM hmin hmax
  have h27 := size_bound_of_andGateClean C hM hf hcl
  omega

/-- The negation of `L-meta-3014` follows from the pair case alone. -/
theorem neg_of_andPairClean (C : Circuit) (hM : Monotone2 C) (hpair : AndPairClean C) :
    ¬ (C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true)) := by
  rintro ⟨h26, hf⟩
  have h27 := size_bound_of_andGateClean C hM hf (andGateClean_of_pairClean C hM hpair)
  omega

end PEqualNP.Outside.L_meta_3014_andand
