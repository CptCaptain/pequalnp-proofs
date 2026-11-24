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

WHAT IS STILL OPEN (the AND-in-AND case). `AndGateClean` is not a consequence of the hypotheses
of `L-meta-3014` alone: an AND gate may be true on a non-edge pair as long as an AND gate above it
blocks the propagation to the output, and such a blocking gate is exactly an AND gate in the cone
of an AND gate. So the missing statement is `AndPairClean` (`andGateClean_of_pairClean` shows it
suffices): an AND gate of a correct circuit is false at `1_uv` for every non-edge `uv`.
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
  ∀ (i : Fin C.gates.length) (u v : Fin 14), ¬ hw.Adj u v →
    (wiresFrom C.gates (List.ofFn (bitsOf {u, v}))).getD (14 + (i : ℕ)) false = false

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
    have h3 := hpair i (0 : Fin 14) 0 (hloop 0)
    rw [h3] at h2
    exact absurd h2 (by simp)
  · -- a singleton is the loop `uu`
    subst hu
    have h3 := hpair i u u (hloop u)
    rw [show ({u, u} : Finset (Fin 14)) = {u} from by simp] at h3
    rw [h3] at hv
    exact absurd hv (by simp)
  · -- a pair: an edge gives the claim, a non-edge contradicts the hypothesis
    subst huv
    by_cases hadj : hw.Adj u v
    · exact ⟨u, v, hadj, by simp [bitsOf], by simp [bitsOf]⟩
    · have h3 := hpair i u v hadj
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
