import PEqualNP.Defs

/-!
# Cut for step L-meta-949 (6-vertex AND-count versus biclique cover)

The step asks for a graph on `Fin 6` whose partial-function AND-count circuit is smaller than
every biclique cover of its edges.  This file cuts that single existential into its two halves,
one hypothesis each:

* `hExists` — the circuit half: a well-formed circuit of size exactly 2 satisfies the
  partial-function condition on some graph on 6 vertices.  No cover appears here.  This half is
  cheap: a cover with `k` bicliques always yields a `k`-gate circuit whose value at `U` is
  "`U` meets both sides of some covering biclique", and at an independent `U` no covering
  biclique is true, so every graph of cover number 2 supplies such a pair.
* `hSep` — the separation half: for EVERY graph on 6 vertices, a well-formed circuit of size 2
  with the partial-function condition already excludes every cover with at most 2 bicliques.
  This is the actual content of the row on 6 vertices, and it is exactly what the enumeration
  of the graphs on 6 vertices (cover numbers by brute force, circuits one gate smaller) decides.

Together they give the statement: take the witness of `hExists` and apply `hSep` to it, using
`C.size = 2` to match the bound `k ≤ C.size` of the statement.
-/

theorem PEqualNP.Outside.R_meta_949_1
    (hExists : ∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6),
      C.WellFormed ∧
      (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
        (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧
      C.size = 2)
    (hSep : ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6),
      C.WellFormed →
      (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
        (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      C.size = 2 →
      ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧
        (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
        (∀ a b : Fin 6, G.Adj a b →
          ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) :
    ∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))) := by
  obtain ⟨G, C, hwf, hpf, hsize⟩ := hExists
  exact ⟨G, C, hwf, hpf, hSep G C hwf hpf hsize⟩
