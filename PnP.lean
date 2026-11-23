/-
# P vs NP – Rigid-Instance Formalization (improved)

Author: Auro Zera (original architecture) + improvements

STATUS: Core Lean 4 only (no Mathlib). Untested against a full Lean build.
This file does NOT prove or refute P = NP.
It proves a complete reduction architecture: P = NP is equivalent to the
non-existence of rigid instances of SAT under finite admissible families
of sound poly-time partial solvers.

The open content remains the named Prop `NoRigid`, never asserted.
-/

namespace PNPRigid

-- ════════════════════════════════════════════════════════════
-- §1 Basic objects
-- ════════════════════════════════════════════════════════════

/-- A decision problem over binary strings. -/
abbrev Lang := List Bool → Prop

/-- A partial solver: `none` = abstain, `some b` = answer `b`. -/
abbrev Solver := List Bool → Option Bool

abbrev Answers (s : Solver) (x : List Bool) : Prop := ∃ b, s x = some b
abbrev Total (s : Solver) : Prop := ∀ x, Answers s x
abbrev Sound (L : Lang) (s : Solver) : Prop :=
  ∀ x b, s x = some b → (L x ↔ b = true)

-- ════════════════════════════════════════════════════════════
-- §2 Abstract complexity model
-- ════════════════════════════════════════════════════════════

/-- A complexity model packaging the standard facts about P, NP,
    poly-time reductions and Cook–Levin.
    Every field is a standard theorem of any concrete model
    (e.g. multi-tape Turing machines). -/
structure CModel where
  P : Lang → Prop
  NP : Lang → Prop
  /-- polynomial-time many-one reducibility -/
  Red : Lang → Lang → Prop
  /-- solver runs in polynomial time whenever it answers -/
  PolyPartial : Solver → Prop
  /-- the canonical NP-complete language (Boolean satisfiability) -/
  sat : Lang
  P_sub_NP : ∀ L, P L → NP L
  P_of_red : ∀ {A B : Lang}, Red A B → P B → P A
  /-- P = languages with a total, sound, poly-time solver -/
  P_iff_total : ∀ L, P L ↔ ∃ s, PolyPartial s ∧ Sound L s ∧ Total s
  /-- finitely many poly-time partial solvers can be combined into one total solver -/
  P_of_cover : ∀ (L : Lang) (l : List Solver),
    (∀ s ∈ l, PolyPartial s ∧ Sound L s) →
    (∀ x, ∃ s ∈ l, Answers s x) → P L
  /-- Cook–Levin -/
  sat_NP : NP sat
  sat_hard : ∀ L, NP L → Red L sat
  /-- reductions are transitive (standard) -/
  Red_trans : ∀ {A B C}, Red A B → Red B C → Red A C
  /-- identity reduction -/
  Red_refl : ∀ L, Red L L

variable (U : CModel)

/-- P = NP. -/
def PeqNP : Prop := ∀ L, U.P L ↔ U.NP L

def NPComplete (L : Lang) : Prop := U.NP L ∧ ∀ A, U.NP A → U.Red A L

theorem sat_complete : NPComplete U U.sat := ⟨U.sat_NP, U.sat_hard⟩

-- ════════════════════════════════════════════════════════════
-- §3 Reduction to a single generator
-- ════════════════════════════════════════════════════════════

/-- **P = NP iff one NP-complete language is in P.** -/
theorem PeqNP_iff_complete_in_P {L : Lang} (hL : NPComplete U L) :
    PeqNP U ↔ U.P L :=
  ⟨fun h => (h L).2 hL.1,
   fun hP A => ⟨U.P_sub_NP A, fun hA => U.P_of_red (hL.2 A hA) hP⟩⟩

theorem not_PeqNP_iff_sat_hard : ¬ PeqNP U ↔ ¬ U.P U.sat :=
  not_congr (PeqNP_iff_complete_in_P U (sat_complete U))

/-- If P ≠ NP then every NP-complete language lies outside P. -/
theorem hard_propagates (h : ¬ PeqNP U) {L : Lang} (hL : NPComplete U L) :
    ¬ U.P L :=
  fun hP => h ((PeqNP_iff_complete_in_P U hL).2 hP)

-- ════════════════════════════════════════════════════════════
-- §4 Rigid instances
-- ════════════════════════════════════════════════════════════

/-- `x` is covered by the family `l` if some solver in `l` answers on it. -/
abbrev Covered (l : List Solver) (x : List Bool) : Prop :=
  ∃ s ∈ l, Answers s x

/-- `x` is rigid for `l`: no solver in the family answers on it. -/
abbrev Rigid (l : List Solver) (x : List Bool) : Prop := ¬ Covered l x

/-- Dichotomy: every instance is either covered or rigid. -/
theorem covered_or_rigid (l : List Solver) (x : List Bool) :
    Covered l x ∨ Rigid l x :=
  Classical.em _

/-- Rigidity is anti-monotone: larger families can only eliminate rigid instances. -/
theorem rigid_mono {l l' : List Solver} (h : ∀ s ∈ l, s ∈ l') {x : List Bool}
    (hr : Rigid l' x) : Rigid l x := by
  rintro ⟨s, hs, ha⟩
  exact hr ⟨s, h s hs, ha⟩

/-- Admissible family: finitely many sound poly-time partial solvers. -/
abbrev Admissible (L : Lang) (l : List Solver) : Prop :=
  ∀ s ∈ l, U.PolyPartial s ∧ Sound L s

/-- **The open hypothesis**: some finite admissible family leaves no rigid instance. -/
abbrev NoRigid (L : Lang) : Prop :=
  ∃ l : List Solver, Admissible U L l ∧ ∀ x, ¬ Rigid l x

-- ════════════════════════════════════════════════════════════
-- §5 Equivalence of P and absence of rigid instances
-- ════════════════════════════════════════════════════════════

theorem P_iff_noRigid (L : Lang) : U.P L ↔ NoRigid U L := by
  constructor
  · intro hP
    obtain ⟨s, hs, hsound, htot⟩ := (U.P_iff_total L).1 hP
    refine ⟨[s], ?_, ?_⟩
    · intro t ht
      have : t = s := by simpa using ht
      subst this
      exact ⟨hs, hsound⟩
    · intro x hr
      exact hr ⟨s, by simp, htot x⟩
  · rintro ⟨l, hadm, hno⟩
    refine U.P_of_cover L l hadm ?_
    intro x
    exact Classical.not_not.1 (hno x)

/-- **Main theorem.** For any NP-complete language L:
    P = NP  ⇔  L has a finite admissible covering family with no rigid instances. -/
theorem PeqNP_iff_noRigid_of_complete {L : Lang} (hL : NPComplete U L) :
    PeqNP U ↔ NoRigid U L :=
  (PeqNP_iff_complete_in_P U hL).trans (P_iff_noRigid U L)

theorem PeqNP_iff_sat_noRigid : PeqNP U ↔ NoRigid U U.sat :=
  PeqNP_iff_noRigid_of_complete U (sat_complete U)

/-- **Separation form.** P ≠ NP iff every finite admissible family for SAT
    leaves at least one rigid instance. This is the precise shape of any proof
    that P ≠ NP. -/
theorem not_PeqNP_iff_rigid_exists :
    ¬ PeqNP U ↔ ∀ l : List Solver, Admissible U U.sat l → ∃ x, Rigid l x := by
  rw [PeqNP_iff_sat_noRigid U]
  constructor
  · intro h l hl
    exact Classical.byContradiction fun hx =>
      h ⟨l, hl, fun x hr => hx ⟨x, hr⟩⟩
  · rintro h ⟨l, hl, hno⟩
    obtain ⟨x, hx⟩ := h l hl
    exact hno x hx

/-- A witness for NoRigid on SAT immediately yields P = NP. -/
theorem PeqNP_of_noRigid (h : NoRigid U U.sat) : PeqNP U :=
  (PeqNP_iff_sat_noRigid U).2 h

/-- Conversely, P = NP yields a trivial one-element covering family. -/
theorem noRigid_of_PeqNP (h : PeqNP U) : NoRigid U U.sat :=
  (PeqNP_iff_sat_noRigid U).1 h

-- ════════════════════════════════════════════════════════════
-- §6 Why finite lists are essential (the obstruction)
-- ════════════════════════════════════════════════════════════

abbrev InfiniteFamily := Nat → Solver

abbrev InfiniteCover (F : InfiniteFamily) (L : Lang) : Prop :=
  (∀ n, U.PolyPartial (F n) ∧ Sound L (F n)) ∧
  (∀ x, ∃ n, Answers (F n) x)

theorem infinite_cover_not_forced_to_P :
    -- The following is *not* a theorem of CModel:
    -- ∀ L F, InfiniteCover U F L → U.P L
    True := trivial

-- ════════════════════════════════════════════════════════════
-- §7 What this formalization actually proves
-- ════════════════════════════════════════════════════════════

/-!
## Summary of proved statements

Inside any model satisfying the fields of `CModel` (i.e., any reasonable
concrete complexity model):

1. P = NP  ⇔  SAT ∈ P.
2. SAT ∈ P  ⇔  there exists a finite list of sound poly-time partial solvers
   that together decide every instance of SAT (no rigid instances remain).
3. Therefore:
   P = NP  ⇔  NoRigid U U.sat.
4. Equivalently:
   P ≠ NP  ⇔  every finite admissible family of partial solvers for SAT
   leaves at least one rigid instance.

These are the precise reduction theorems. They do not decide the equality;
they only restate it in the language of rigid instances.

Any future proof or refutation of P vs NP must establish or refute the
existence of a finite covering family for SAT (or equivalently produce a
single total poly-time solver). The known barriers (relativization, natural
proofs, algebrization) still apply; this formalization is oracle-agnostic
and does not bypass them.
-/

end PNPRigid
