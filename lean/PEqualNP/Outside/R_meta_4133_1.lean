import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A near-minimal top-form circuit whose charging count is at most four leaves at most four of
-- the eleven edges uncovered, and no uncovered set of that size gives one of the seventeen
-- excluded masks.
theorem PEqualNP.Outside.R_meta_4133_1
    (hCharge :
      ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ (4 : ℕ))
    (hMask :
      ∀ (S : Finset (Sym2 (Fin (11 : ℕ)))),
        S.card ≤ (4 : ℕ) →
          BitVec.ofNat (16 : ℕ) (PEqualNP.MetaComplexity.tableIndex fun (x4 : Fin (16 : ℕ)) =>
            have x5 : ℕ × ℕ := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))].getD ↑x4 ((0 : ℕ), (0 : ℕ));
            Decidable.decide (s(Fin.ofNat (11 : ℕ) x5.1, Fin.ofNat (11 : ℕ) x5.2) ∈ S)) ∉ [(36608 : BitVec (16 : ℕ)), (44800 : BitVec (16 : ℕ)), (44864 : BitVec (16 : ℕ)), (44992 : BitVec (16 : ℕ)), (48960 : BitVec (16 : ℕ)), (52992 : BitVec (16 : ℕ)), (53120 : BitVec (16 : ℕ)), (53184 : BitVec (16 : ℕ)), (57216 : BitVec (16 : ℕ)), (61184 : BitVec (16 : ℕ)), (61248 : BitVec (16 : ℕ)), (61312 : BitVec (16 : ℕ)), (61376 : BitVec (16 : ℕ)), (65280 : BitVec (16 : ℕ)), (65344 : BitVec (16 : ℕ)), (65408 : BitVec (16 : ℕ)), (65472 : BitVec (16 : ℕ))])
    : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; have x3 : Finset (Sym2 (Fin (11 : ℕ))) → BitVec (16 : ℕ) := fun (x3 : Finset (Sym2 (Fin (11 : ℕ)))) =>   BitVec.ofNat (16 : ℕ)     (PEqualNP.MetaComplexity.tableIndex fun (x4 : Fin (16 : ℕ)) =>       have x5 : ℕ × ℕ := x1.getD ↑x4 ((0 : ℕ), (0 : ℕ));       Decidable.decide (s(Fin.ofNat (11 : ℕ) x5.1, Fin.ofNat (11 : ℕ) x5.2) ∈ x3)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x4 →       PEqualNP.TopForm.TopForm x2 x4 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →           have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;           have x10 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;           x9.card ≤ x10 → x10 < (2 : ℕ) * x9.card → x3 x9 ∉ [(36608 : BitVec (16 : ℕ)), (44800 : BitVec (16 : ℕ)), (44864 : BitVec (16 : ℕ)), (44992 : BitVec (16 : ℕ)), (48960 : BitVec (16 : ℕ)), (52992 : BitVec (16 : ℕ)), (53120 : BitVec (16 : ℕ)), (53184 : BitVec (16 : ℕ)), (57216 : BitVec (16 : ℕ)), (61184 : BitVec (16 : ℕ)), (61248 : BitVec (16 : ℕ)), (61312 : BitVec (16 : ℕ)), (61376 : BitVec (16 : ℕ)), (65280 : BitVec (16 : ℕ)), (65344 : BitVec (16 : ℕ)), (65408 : BitVec (16 : ℕ)), (65472 : BitVec (16 : ℕ))] := by
  intro x1 x2 x3 C hsize hleast htop hjunk x9 x10 hle hlt
  have hch := hCharge x2 C rfl hleast htop
  have hcard : x9.card ≤ 4 := by omega
  exact hMask x9 hcard
