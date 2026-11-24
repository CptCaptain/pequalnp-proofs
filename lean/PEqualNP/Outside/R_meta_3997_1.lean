import Mathlib
import PEqualNP.Defs

/-! A reduction for step `L-meta-3997`: the graph side (a non-adjacent pair of vertices,
supplied by `Hgraph`) and the circuit side (deleting that pair buys eight gates, supplied by
`Hcirc`) are kept apart; the step follows from the two. -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3997_1
    (Hgraph : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),
    (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) →
    (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) →
    (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
    (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
    ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15)
    (Hcirc : ∀ (x1 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x11 : ℕ) (x14 x15 : Fin x1),
    x11 + (1 : ℕ) < (2 : ℕ) * x1 →
    PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 →
    ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x17 : Fin x1 → Bool) =>
          x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  intro x1 x2 x3 h30 hEven hCol hDeg hGirth hedge hOR x11 hx11 hsize
  obtain ⟨x14, x15, hne, hnon⟩ := Hgraph x1 x2 h30 hEven hCol hDeg hGirth hedge
  obtain ⟨x16, h16, hcs⟩ := Hcirc x1 x3 x11 x14 x15 hx11 hsize
  exact ⟨x14, x15, hne, hnon, x16, h16, hcs⟩
