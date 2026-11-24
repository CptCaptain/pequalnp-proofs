import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_1983

/-!
# Towards the negation of `L-meta-3014`: no 26-gate AO2 circuit for the Heawood edges

`PEqualNP.Outside.L_meta_1983` proves: a circuit `C` on 14 inputs that is `Monotone2`, reads
back (`NestedCover.ReadsBack 14`), has no AND gate strictly inside the cone of an AND gate, and
computes the 21-edge function of the Heawood graph, has at least 27 gates.

`L-meta-3014` claims the opposite side of that bound: a circuit in the `IsAO2 14` model, with
distinct gate inputs, of size between 2 and 26, that agrees with the Heawood edge function on
every minimal true point and every maximal false point.

This file assembles the reduction from the `L-meta-3014` statement to the hypotheses of
`L_meta_1983`:

* `isAO2_monotone2` — `IsAO2 n C` gives `Monotone2 C` (the fan-in bound is `= 2`).
* `isAO2_readsBack` — `IsAO2 n C` gives `ReadsBack n C` (a projection).
* `eval_mono` — a `Monotone2` circuit is monotone as a function.
* `exists_min_bits` / `exists_max_bits` — every input has a minimal edge-containing subset and a
  maximal edge-free superset.
* `eval_iff_hw` — the two local conditions of `L-meta-3014` ("every minimal true point of the
  Heawood function is true", "every maximal false point is false") together with monotonicity
  give `C.eval x = hwFun x` for **every** `x`, not only for the extremal ones.
* `neg_of_noAndAndInCone` — the negation of the `L-meta-3014` existential, under the one
  hypothesis the 1983 theorem still needs and this file does not supply: no AND gate strictly
  inside the cone of another AND gate. `neg_of_topForm` isolates that hypothesis as a single
  normalisation statement.

The missing piece, stated plainly: an `IsAO2 14` circuit of size `≤ 26` for the Heawood function
may well have an AND gate inside the cone of an AND gate, and then `L_meta_1983` does not apply.
What is needed is the top-form normalisation — from any such circuit build one with no such pair
and with no more gates — or a direct 27-gate bound for the circuits that do have the pair. Neither
is proved here.
-/

namespace PEqualNP.Outside.L_meta_3014_neg

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

/-- The 21 edges of the Heawood graph on the vertices `Fin 14`. -/
def hwEdges : List (ℕ × ℕ) :=
  [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)),
   ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)),
   ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)),
   ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)),
   ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)),
   ((6 : ℕ), (11 : ℕ))]

/-- The Heawood edge function on 14 inputs: true on an input containing both ends of an edge. -/
def hwFun (x : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 14, (p.val, l.val) ∈ hwEdges ∧ x p = true ∧ x l = true)

lemma hwFun_iff (x : Fin 14 → Bool) :
    hwFun x = true ↔ ∃ p l : Fin 14, (p.val, l.val) ∈ hwEdges ∧ x p = true ∧ x l = true := by
  unfold hwFun
  exact decide_eq_true_iff

lemma hwFun_false_iff (x : Fin 14 → Bool) :
    hwFun x = false ↔ ¬ ∃ p l : Fin 14, (p.val, l.val) ∈ hwEdges ∧ x p = true ∧ x l = true := by
  constructor
  · intro h ⟨p, l, he, hp, hl⟩
    have h' := (hwFun_iff x).2 ⟨p, l, he, hp, hl⟩
    rw [h] at h'
    exact Bool.false_ne_true h'
  · intro h
    rcases hb : hwFun x with - | -
    · rfl
    · exact absurd ((hwFun_iff x).1 hb) h

/-- No entry of the Heawood edge list is a loop. -/
lemma hw_no_loop {p l : ℕ} (h : (p, l) ∈ hwEdges) : p ≠ l := by
  simp only [hwEdges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

/-- The bit vector of a set of vertices. -/
def bitsOf (S : Finset (Fin 14)) : Fin 14 → Bool := fun i => decide (i ∈ S)

lemma bitsOf_true {S : Finset (Fin 14)} {i : Fin 14} : bitsOf S i = true ↔ i ∈ S := by
  unfold bitsOf
  exact decide_eq_true_iff

lemma bitsOf_le {S T : Finset (Fin 14)} (h : S ⊆ T) :
    ∀ i, bitsOf S i = true → bitsOf T i = true := by
  intro i hi
  rw [bitsOf_true] at hi ⊢
  exact h hi

lemma le_bitsOf {S T : Finset (Fin 14)} (h : ∀ i, bitsOf S i = true → bitsOf T i = true) :
    S ⊆ T := by
  intro i hi
  exact bitsOf_true.1 (h i (bitsOf_true.2 hi))

/-- `hwFun` on the bit vector of a set: some edge lies inside the set. -/
lemma hwFun_bitsOf_true {S : Finset (Fin 14)} :
    hwFun (bitsOf S) = true ↔ ∃ p ∈ S, ∃ l ∈ S, (p.val, l.val) ∈ hwEdges := by
  rw [hwFun_iff]
  constructor
  · rintro ⟨p, l, he, hp, hl⟩
    exact ⟨p, bitsOf_true.1 hp, l, bitsOf_true.1 hl, he⟩
  · rintro ⟨p, hp, l, hl, he⟩
    exact ⟨p, l, he, bitsOf_true.2 hp, bitsOf_true.2 hl⟩

lemma hwFun_bitsOf_false {S : Finset (Fin 14)} :
    hwFun (bitsOf S) = false ↔ ∀ p ∈ S, ∀ l ∈ S, (p.val, l.val) ∉ hwEdges := by
  rw [hwFun_false_iff]
  constructor
  · intro h p hp l hl he
    exact h ⟨p, l, he, bitsOf_true.2 hp, bitsOf_true.2 hl⟩
  · rintro h ⟨p, l, he, hp, hl⟩
    exact h p (bitsOf_true.1 hp) l (bitsOf_true.1 hl) he

/-- `Bool` order is implication. -/
lemma bool_le_iff {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

/-- Pointwise `Bool` order is pointwise implication. -/
lemma pi_le_iff {n : ℕ} {x y : Fin n → Bool} :
    x ≤ y ↔ ∀ i, x i = true → y i = true := by
  rw [Pi.le_def]
  exact forall_congr' fun i => bool_le_iff

/-! ### Step 1: the hypotheses of the 1983 theorem follow from `IsAO2` -/

lemma isAO2_monotone2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  obtain ⟨hAO, -, hlen⟩ := h
  intro g hg
  refine ⟨?_, ?_⟩
  · rcases hAO g hg with h' | h'
    · simp [h']
    · simp [h']
  · rw [hlen g hg]

lemma isAO2_readsBack {n : ℕ} {C : Circuit} (h : IsAO2 n C) : ReadsBack n C := h.2.1

lemma monotone2_andOrOnly {C : Circuit} (h : Monotone2 C) : AndOrOnly C := by
  intro g hg
  have h' := (h g hg).1
  simpa using h'

/-! ### Step 2: monotonicity of the evaluated function -/

/-- A circuit of AND and OR gates is monotone as a function of its input bits. -/
lemma eval_mono {C : Circuit} (hAO : AndOrOnly C) {x y : Fin 14 → Bool}
    (hxy : ∀ i, x i = true → y i = true) (h : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hle : ∀ i, (List.ofFn x : List Bool).getD i false = true →
      (List.ofFn y : List Bool).getD i false = true := by
    intro i hi
    by_cases hi' : i < 14
    · rw [List.getD_eq_getElem _ _ (by simpa using hi')] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi')] at hi
      exact absurd hi (by simp)
  have hw := PEqualNP.Outside.L_meta_1983.wiresFrom_mono C.gates hAO (List.ofFn x)
    (List.ofFn y) (by simp) hle C.output h
  have h' : (C.wires (List.ofFn y)).getD C.output false = true := hw
  simpa [Circuit.eval] using h'

/-! ### Step 3: extremal inputs

Every input containing an edge has a minimal such subset of size two, and every input containing
no edge has a maximal edge-free superset. -/

lemma exists_min_bits {x : Fin 14 → Bool} (hx : hwFun x = true) :
    ∃ x6 : Fin 14 → Bool, (∀ i, x6 i = true → x i = true) ∧ hwFun x6 = true ∧
      ∀ x7, (∀ i, x7 i = true → x6 i = true) → hwFun x7 = true → x7 = x6 := by
  obtain ⟨p, l, he, hp, hl⟩ := (hwFun_iff x).1 hx
  have hpl : p.val ≠ l.val := hw_no_loop he
  refine ⟨bitsOf {p, l}, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ ({p, l} : Finset (Fin 14)) := bitsOf_true.1 hi
    rcases Finset.mem_insert.1 hi' with h | h
    · rw [h]; exact hp
    · rw [Finset.mem_singleton.1 h]; exact hl
  · exact (hwFun_bitsOf_true).2 ⟨p, Finset.mem_insert_self p {l}, l,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self l), he⟩
  · intro x7 hx7 h7
    obtain ⟨a, b, hab, ha, hb⟩ := (hwFun_iff x7).1 h7
    have hab' : a.val ≠ b.val := hw_no_loop hab
    have hamem : a ∈ ({p, l} : Finset (Fin 14)) := bitsOf_true.1 (hx7 a ha)
    have hbmem : b ∈ ({p, l} : Finset (Fin 14)) := bitsOf_true.1 (hx7 b hb)
    have hset : ({a, b} : Finset (Fin 14)) = {p, l} := by
      have ha' : a = p ∨ a = l := by simpa using hamem
      have hb' : b = p ∨ b = l := by simpa using hbmem
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hab'
      · rfl
      · exact Finset.pair_comm _ _
      · exact absurd rfl hab'
    have hx7iff : ∀ i, x7 i = true ↔ i ∈ ({a, b} : Finset (Fin 14)) := by
      intro i
      constructor
      · intro h
        have h' : bitsOf ({p, l} : Finset (Fin 14)) i = true := hx7 i h
        rw [← hset] at h'
        exact bitsOf_true.1 h'
      · intro h
        rcases Finset.mem_insert.1 h with h' | h'
        · rw [h']; exact ha
        · rw [Finset.mem_singleton.1 h']; exact hb
    funext i
    rw [← hset, bitsOf]
    by_cases hi : i ∈ ({a, b} : Finset (Fin 14))
    · rw [decide_eq_true hi, (hx7iff i).2 hi]
    · rw [decide_eq_false hi]
      by_contra hcon
      exact hi ((hx7iff i).1 (by simpa using hcon))

lemma exists_max_bits {x : Fin 14 → Bool} (hx : hwFun x = false) :
    ∃ x6 : Fin 14 → Bool, (∀ i, x i = true → x6 i = true) ∧ hwFun x6 = false ∧
      ∀ x7, (∀ i, x6 i = true → x7 i = true) → hwFun x7 = false → x7 = x6 := by
  classical
  set X : Finset (Fin 14) := Finset.univ.filter (fun i => x i = true) with hX
  have hXmem : ∀ i, i ∈ X ↔ x i = true := by
    intro i
    simp [hX]
  set A : Finset (Finset (Fin 14)) := Finset.univ.powerset.filter
    (fun S => X ⊆ S ∧ ∀ p ∈ S, ∀ l ∈ S, (p.val, l.val) ∉ hwEdges) with hA
  have hXA : X ∈ A := by
    rw [hA, Finset.mem_filter]
    refine ⟨Finset.mem_powerset.2 (Finset.subset_univ X), Finset.Subset.refl X, ?_⟩
    intro p hp l hl he
    have hp' : x p = true := (hXmem p).1 hp
    have hl' : x l = true := (hXmem l).1 hl
    have := (hwFun_iff x).2 ⟨p, l, he, hp', hl'⟩
    rw [hx] at this
    exact Bool.false_ne_true this
  have hAne : A.Nonempty := ⟨X, hXA⟩
  let m := (A.image Finset.card).max' (hAne.image Finset.card)
  have hmmem : m ∈ A.image Finset.card := Finset.max'_mem _ _
  obtain ⟨S, hSA, hSm⟩ := Finset.mem_image.1 hmmem
  have hSle : ∀ T ∈ A, T.card ≤ S.card := by
    intro T hT
    have h1 : T.card ≤ m := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hT)
    omega
  obtain ⟨hXS, hSfree⟩ := (Finset.mem_filter.1 hSA).2
  refine ⟨bitsOf S, ?_, ?_, ?_⟩
  · intro i hi
    exact bitsOf_true.2 (hXS ((hXmem i).2 hi))
  · exact (hwFun_bitsOf_false).2 hSfree
  · intro x7 hx7 h7
    set T : Finset (Fin 14) := Finset.univ.filter (fun i => x7 i = true) with hT
    have hTmem : ∀ i, i ∈ T ↔ x7 i = true := by
      intro i
      simp [hT]
    have hST : S ⊆ T := by
      intro i hi
      exact (hTmem i).2 (hx7 i (bitsOf_true.2 hi))
    have hTA : T ∈ A := by
      rw [hA, Finset.mem_filter]
      refine ⟨Finset.mem_powerset.2 (Finset.subset_univ T), ?_, ?_⟩
      · intro i hi
        exact hST (hXS hi)
      · intro p hp l hl he
        have hp' : x7 p = true := (hTmem p).1 hp
        have hl' : x7 l = true := (hTmem l).1 hl
        have := (hwFun_iff x7).2 ⟨p, l, he, hp', hl'⟩
        rw [h7] at this
        exact Bool.false_ne_true this
    have hcard : T.card ≤ S.card := hSle T hTA
    have hTS : S = T := Finset.eq_of_subset_of_card_le hST hcard
    funext i
    rw [hTS, bitsOf]
    by_cases hi : i ∈ T
    · rw [decide_eq_true hi, (hTmem i).1 hi]
    · rw [decide_eq_false hi]
      by_contra hcon
      exact hi ((hTmem i).2 (by simpa using hcon))

/-! ### Step 4: the two local conditions give the full function -/

lemma eval_iff_hw {C : Circuit} (hM : Monotone2 C)
    (hmin : ∀ x : Fin 14 → Bool, hwFun x = true →
      (∀ x6, x6 ≤ x → hwFun x6 = true → x6 = x) → C.eval (List.ofFn x) = true)
    (hmax : ∀ x : Fin 14 → Bool, hwFun x = false →
      (∀ x6, x ≤ x6 → hwFun x6 = false → x6 = x) → C.eval (List.ofFn x) = false) :
    ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true := by
  have hAO := monotone2_andOrOnly hM
  intro x
  constructor
  · intro hev
    by_contra hcon
    have hxf : hwFun x = false := by
      rcases hb : hwFun x with - | -
      · rfl
      · exact absurd hb hcon
    obtain ⟨x6, hx6le, hx6f, hx6max⟩ := exists_max_bits hxf
    have hle : x ≤ x6 := (pi_le_iff).2 hx6le
    have hx6ev : C.eval (List.ofFn x6) = false := hmax x6 hx6f (by
      intro x7 hle' h7
      exact hx6max x7 ((pi_le_iff).1 hle') h7)
    have hmono : C.eval (List.ofFn x6) = true :=
      eval_mono hAO ((pi_le_iff).1 hle) hev
    rw [hx6ev] at hmono
    exact Bool.false_ne_true hmono
  · intro hfun
    obtain ⟨x6, hx6le, hx6t, hx6min⟩ := exists_min_bits hfun
    have hmin' : C.eval (List.ofFn x6) = true := hmin x6 hx6t (by
      intro x7 hle' h7
      exact hx6min x7 ((pi_le_iff).1 hle') h7)
    exact eval_mono hAO hx6le hmin'

/-! ### Step 5: the negation, with the top-form hypothesis still needed -/

/-- The statement of `L-meta-3014`, with the single hypothesis the 1983 theorem needs kept
explicit: no AND gate lies strictly inside the cone of another AND gate. Negating it is what the
missing top-form normalisation would give. -/
def NegTarget (hnoAndAnd : Circuit → Prop) : Prop :=
  ¬ ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 2 ≤ C.size ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, hwFun x = true →
      (∀ x6, x6 ≤ x → hwFun x6 = true → x6 = x) → C.eval (List.ofFn x) = true) ∧
    (∀ x : Fin 14 → Bool, hwFun x = false →
      (∀ x6, x ≤ x6 → hwFun x6 = false → x6 = x) → C.eval (List.ofFn x) = false) ∧
    hnoAndAnd C

/-- The 1983 lower bound applies to every `IsAO2` circuit that has no AND gate inside the cone of
an AND gate. -/
theorem neg_of_noAndAndInCone :
    NegTarget (fun C => ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧
      (gateAt C j).op = GateOp.and ∧ InCone 14 C i j) := by
  rintro ⟨C, hAO2, -, -, h26, hmin, hmax, hno⟩
  have hM : Monotone2 C := isAO2_monotone2 hAO2
  have hRB : ReadsBack 14 C := isAO2_readsBack hAO2
  have hf := eval_iff_hw hM hmin hmax
  have hf' : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = Bool.true ↔
      ∃ p l : Fin 14, (p.val, l.val) ∈ hwEdges ∧ x p = Bool.true ∧ x l = Bool.true :=
    fun x => (hf x).trans (hwFun_iff x)
  have hbound := PEqualNP.Outside.L_meta_1983 C hM hRB hno hf'
  omega

/-- The same negation, with the missing top-form normalisation isolated as a single hypothesis:
any circuit meeting the `L-meta-3014` conditions (which, by `eval_iff_hw`, computes the Heawood
function everywhere) is replaced by one that computes the same function, has no more gates, and
has no AND gate inside the cone of an AND gate. -/
theorem neg_of_topForm
    (topForm : ∀ C : Circuit, IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.size ≤ 26 →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hwFun x = true) →
      ∃ D : Circuit, IsAO2 14 D ∧ D.size ≤ C.size ∧
        (¬ ∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧ (gateAt D j).op = GateOp.and ∧
          InCone 14 D i j) ∧
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hwFun x = true)) :
    NegTarget (fun _ => True) := by
  rintro ⟨C, hAO2, hnd, -, h26, hmin, hmax, -⟩
  have hM : Monotone2 C := isAO2_monotone2 hAO2
  have hf := eval_iff_hw hM hmin hmax
  obtain ⟨D, hDAO2, hDsize, hDno, hDf⟩ := topForm C hAO2 hnd h26 hf
  have hbound := PEqualNP.Outside.L_meta_1983 D (isAO2_monotone2 hDAO2)
    (isAO2_readsBack hDAO2) hDno (fun x => (hDf x).trans (hwFun_iff x))
  omega

end PEqualNP.Outside.L_meta_3014_neg
