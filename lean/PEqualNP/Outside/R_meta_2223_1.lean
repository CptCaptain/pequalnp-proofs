import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Reduction for step `L-meta-2223` (Fano incidence, no circuit of at most 27 gates).
--
-- The step quantifies over an arbitrary fan-in-two circuit `C` of size at most 27 that computes
-- the Fano incidence function, and asks for a circuit that reads no gate wire twice and keeps
-- both line degrees at least two. The witness never uses `C`: the hypotheses about `C` are
-- irrelevant, so the step splits into two parts, both genuinely weaker than the statement:
--   h1: for every incident point/line pair there is a fan-in-two circuit of size at most 27
--       that computes the incidence and has both line degrees at least two (construction);
--   h2: any such circuit can be replaced by one that also reads no gate wire twice (repair).

theorem PEqualNP.Outside.R_meta_2223_1
    (h1 : let G : Circuit → Prop := fun (C : Circuit) =>
        C.size ≤ (27 : ℕ) ∧
          (∀ (j : ℕ) (g : Gate), C.gates[j]? = Option.some g →
            (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
              ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < (14 : ℕ) + j ∧ b < (14 : ℕ) + j) ∧
          (∀ x : Fin (14 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
            ∃ u t : Fin (7 : ℕ),
              (u = t ∨ u = t + (1 : Fin (7 : ℕ)) ∨ u = t + (3 : Fin (7 : ℕ))) ∧
                x (Fin.castAdd (7 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) t) = Bool.true);
      ∀ (p q : Fin (7 : ℕ)),
        (p = q ∨ p = q + (1 : Fin (7 : ℕ)) ∨ p = q + (3 : Fin (7 : ℕ))) →
          ∃ C' : Circuit, G C' ∧
            (2 : ℕ) ≤ C'.lineDeg (14 : ℕ) {↑p} ∧ (2 : ℕ) ≤ C'.lineDeg (14 : ℕ) {(7 : ℕ) + ↑q})
    (h2 : let G : Circuit → Prop := fun (C : Circuit) =>
        C.size ≤ (27 : ℕ) ∧
          (∀ (j : ℕ) (g : Gate), C.gates[j]? = Option.some g →
            (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
              ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < (14 : ℕ) + j ∧ b < (14 : ℕ) + j) ∧
          (∀ x : Fin (14 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
            ∃ u t : Fin (7 : ℕ),
              (u = t ∨ u = t + (1 : Fin (7 : ℕ)) ∨ u = t + (3 : Fin (7 : ℕ))) ∧
                x (Fin.castAdd (7 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) t) = Bool.true);
      let R : Circuit → Prop := fun (C : Circuit) =>
        (List.filter (fun (w : ℕ) => Decidable.decide ((14 : ℕ) ≤ w))
          (C.output :: List.flatMap Gate.inputs C.gates)).Nodup;
      ∀ (C : Circuit) (p q : Fin (7 : ℕ)), G C →
        (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {↑p} → (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {(7 : ℕ) + ↑q} →
          ∃ C' : Circuit, G C' ∧ R C' ∧
            (2 : ℕ) ≤ C'.lineDeg (14 : ℕ) {↑p} ∧
              (2 : ℕ) ≤ C'.lineDeg (14 : ℕ) {(7 : ℕ) + ↑q}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  exact fun (C : Circuit) (p q : Fin (7 : ℕ)) (hC : _) (hp : _) (hd1 : _) (hd2 : _) => by
    obtain ⟨C', hG', hd1', hd2'⟩ := h1 p q hp
    exact h2 C' p q hG' hd1' hd2'
