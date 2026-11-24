import Mathlib
import PEqualNP.Defs

/-!
The `IsAO2` bridge to the 1983 lower bound.

`PEqualNP.Outside.L_meta_1983` takes three hypotheses on a circuit `C` on `n` inputs: it is
`Monotone2` (AND and OR gates of fan-in at most two), it reads back
(`PEqualNP.MetaComplexity.NestedCover.ReadsBack n C`), and it has no AND gate strictly inside the
cone of an AND gate. The statement `L-meta-3014` describes its circuit instead by the `IsAO2 n`
model together with two local conditions: the circuit is true on every minimal true point of the
target function and false on every maximal false point.

This file supplies the first two of those three hypotheses from the `L-meta-3014` side.

  shape3014_monotone2
    the gate-shape half of the prerequisites (AND and OR only, fan-in exactly two) already gives
    `Monotone2 C`; the bound `at most two` follows from the equality `exactly two`.

  isao2_monotone2
    the same conclusion from `IsAO2 n C`.

  isao2_readsBack
    `IsAO2 n C` gives `ReadsBack n C`.

  isao2_iff_shape_readsBack
    `IsAO2 n C` is exactly the gate shape plus `ReadsBack n C`, so the second conclusion is a
    projection of the definition and not new mathematics.

  exists_shape_extremal_not_readsBack
    the ordering condition is nevertheless a real hypothesis: the gate shape together with the two
    local conditions of `L-meta-3014` does not give `ReadsBack`. The witness is a one-gate circuit
    whose AND gate reads its own wire, so that wire does not exist when the gate is evaluated and
    the circuit is false everywhere; it satisfies both local conditions for the everywhere false
    function and fails `ReadsBack 1`.

What this file does not do. The third hypothesis of the 1983 theorem, no AND gate inside the cone
of an AND gate, does not follow from the `L-meta-3014` prerequisites and is not proved here. The
step from the two local conditions to the full function is `eval_iff_hw` in the file
`PEqualNP.Outside.L_meta_3014_neg`, which is not in this branch.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3014_isao2

/-! The gate shape of `L-meta-3014` and its two local conditions. -/

/-- The gate-shape half of the `L-meta-3014` prerequisites: AND and OR gates only, each reading
exactly two wires. This is `IsAO2` without the ordering condition `ReadsBack`. -/
def Shape3014 (C : Circuit) : Prop :=
  AndOrOnly C ∧ ∀ g ∈ C.gates, g.inputs.length = 2

/-- The two local conditions of `L-meta-3014` for a Boolean function `f` on `n` inputs: `C` is
true on every minimal true point of `f` and false on every maximal false point of `f`. -/
def ExtremalOK (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  (∀ x : Fin n → Bool, f x = true → (∀ y : Fin n → Bool, y ≤ x → f y = true → y = x) →
      C.eval (List.ofFn x) = true) ∧
    ∀ x : Fin n → Bool, f x = false → (∀ y : Fin n → Bool, x ≤ y → f y = false → y = x) →
      C.eval (List.ofFn x) = false

/-! `Monotone2` from the gate shape. -/

/-- The gate shape of `L-meta-3014` gives the fan-in-two monotone model: AND and OR gates are in
the allowed basis, and reading exactly two wires is reading at most two. -/
theorem shape3014_monotone2 {C : Circuit} (h : Shape3014 C) : Monotone2 C := by
  obtain ⟨hAO, hlen⟩ := h
  intro g hg
  refine ⟨?_, ?_⟩
  · rcases hAO g hg with h' | h'
    · simp [h']
    · simp [h']
  · rw [hlen g hg]

/-- `IsAO2` gives `Monotone2`, through the gate shape. -/
theorem isao2_monotone2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C :=
  shape3014_monotone2 ⟨h.1, h.2.2⟩

/-- `IsAO2` gives `ReadsBack`: it is one of its three conjuncts. -/
theorem isao2_readsBack {n : ℕ} {C : Circuit} (h : IsAO2 n C) : ReadsBack n C := h.2.1

/-- `IsAO2 n C` is exactly the gate shape plus `ReadsBack n C`; the two conclusions above are the
two halves of that equivalence. -/
theorem isao2_iff_shape_readsBack {n : ℕ} {C : Circuit} :
    IsAO2 n C ↔ Shape3014 C ∧ ReadsBack n C :=
  ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩

/-! `ReadsBack` does not follow from the gate shape plus the local conditions.

The witness is a single AND gate that reads its own wire. On one input the wires of the circuit are
`[x 0]`; the gate is then evaluated while its wire `1` does not exist yet, so it reads `false`
twice and is `false`, and the output wire `1` reads `false`. The circuit is false everywhere, hence
false on every maximal false point of the everywhere false function, and it has no minimal true
point to be wrong about. It fails `ReadsBack 1` because gate `0` reads the wire `1`, which is not
below `1 + 0`. -/

/-- One AND gate reading its own wire (wire `1` on one input) twice. -/
def badCircuit : Circuit := ⟨[⟨GateOp.and, [1, 1]⟩], 1⟩

theorem badCircuit_shape : Shape3014 badCircuit := by
  refine ⟨?_, ?_⟩
  · intro g hg
    have hg' : g = ⟨GateOp.and, [1, 1]⟩ := by simpa [badCircuit] using hg
    rw [hg']
    exact Or.inl rfl
  · intro g hg
    have hg' : g = ⟨GateOp.and, [1, 1]⟩ := by simpa [badCircuit] using hg
    rw [hg']
    rfl

/-- The circuit is false on every input: its gate reads a wire that does not exist yet. -/
theorem badCircuit_eval (x : Fin 1 → Bool) : badCircuit.eval (List.ofFn x) = false := by
  simp [Circuit.eval, Circuit.wires, badCircuit, GateOp.eval]

theorem badCircuit_not_readsBack : ¬ ReadsBack 1 badCircuit := by
  intro h
  have h' := h 0 (by simp [badCircuit]) 1 (by simp [gateAt, badCircuit])
  exact absurd h' (by simp)

/-- The gate shape plus the two local conditions of `L-meta-3014` do not give `ReadsBack`: a
circuit of that shape that is false everywhere meets both local conditions for the everywhere
false function and still fails `ReadsBack`. -/
theorem exists_shape_extremal_not_readsBack :
    ∃ C : Circuit, Shape3014 C ∧ ExtremalOK 1 (fun _ => false) C ∧ ¬ ReadsBack 1 C := by
  refine ⟨badCircuit, badCircuit_shape, ⟨?_, ?_⟩, badCircuit_not_readsBack⟩
  · intro x hx
    exact absurd hx (by simp)
  · intro x _ _
    exact badCircuit_eval x

end PEqualNP.Outside.L_meta_3014_isao2

theorem PEqualNP.Outside.L_meta_3014_isao2 (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C :=
  ⟨PEqualNP.Outside.L_meta_3014_isao2.isao2_monotone2 h,
    PEqualNP.Outside.L_meta_3014_isao2.isao2_readsBack h⟩
