# P vs NP — Rigid-Instance Formalization

A Lean 4 formalization of a **rigid-instance framework** for expressing the relationship between polynomial-time decision procedures and finite families of sound partial solvers.

The central result is a conditional equivalence:

> Within a complexity model satisfying the assumptions packaged in `CModel`, a language is in **P** if and only if some finite admissible family of partial solvers covers every input. For an NP-complete language such as SAT, this is equivalent to **P = NP**.

This gives a precise language for studying what a separation proof would need to establish: every finite admissible family of partial solvers for SAT must leave at least one input unanswered by every solver in the family.

> [!IMPORTANT]
> **This project does not prove or refute P = NP.** The main results are equivalences derived from the assumptions in `CModel`. The file does not instantiate that structure with a concrete Turing-machine complexity model, and it is currently marked as untested against a full Lean build.

## Status

| Item | Status |
|---|---|
| Proof assistant | Lean 4 |
| Intended dependencies | Lean core only; no Mathlib |
| Main subject | Finite families of sound polynomial-time partial solvers |
| Main open proposition | `NoRigid` |
| Build verification | Builds successfully |
| P vs NP resolved? | Undecided |

## The basic idea

A partial solver is a function

```lean
abbrev Solver := List Bool → Option Bool
```

Its result has three possible meanings:

- `some true`: answer that the input belongs to the language.
- `some false`: answer that the input does not belong to the language.
- `none`: abstain; the solver gives no answer for that input.

A solver is **sound** when every answer it gives is correct. A finite list of sound, polynomial-time partial solvers is **admissible** when every member has those properties.

For a family `l` and input `x`:

- `Covered l x` means at least one solver in `l` answers on `x`.
- `Rigid l x` means no solver in `l` answers on `x`.
- `NoRigid L` means there exists a finite admissible family for `L` with no rigid inputs — every input is covered by at least one member of the family.

The key observation formalized here is that a finite admissible family covering every input is equivalent, under the model's assumptions, to a total sound polynomial-time solver.

## Main formal results

The definitions and theorems live in the `PNPRigid` namespace. The complexity model is supplied as a parameter:

```lean
variable (U : CModel)
```

The principal results are:

### 1. NP-completeness reduces the question to one language

```lean
theorem PeqNP_iff_complete_in_P
```

For any language `L` known to be NP-complete in `U`, the theorem establishes:

\[
P = NP \iff L \in P.
\]

The file also derives the corresponding result for the model's canonical SAT language:

```lean
theorem not_PeqNP_iff_sat_hard
```

### 2. P is equivalent to having no rigid instances

```lean
theorem P_iff_noRigid (L : Lang) : U.P L ↔ NoRigid U L
```

This is the central local equivalence. A language is in `P` exactly when there is a finite admissible family of sound polynomial-time partial solvers that collectively answers every input.

### 3. The P vs NP statement in rigid-instance form

```lean
theorem PeqNP_iff_sat_noRigid
```

For the canonical SAT language:

\[
P = NP \iff \operatorname{NoRigid}(SAT).
\]

Equivalently:

```lean
theorem not_PeqNP_iff_rigid_exists
```

states that

\[
P \ne NP \iff
\text{every finite admissible family for SAT leaves at least one rigid input.}
\]

This is a reformulation of the separation question, not a construction of such a rigid input or a proof that one must exist.

### 4. The two directions are exposed explicitly

The file also provides:

- `PeqNP_of_noRigid`: a `NoRigid` witness for SAT implies `P = NP`.
- `noRigid_of_PeqNP`: `P = NP` implies a `NoRigid` witness for SAT.
- `hard_propagates`: if `P ≠ NP`, every NP-complete language is outside `P` in the model.

## Formal architecture

The file is organized into seven sections:

1. **Basic objects** — languages, partial solvers, answers, totality, and soundness.
2. **Abstract complexity model** — the `CModel` structure and its complexity-theoretic assumptions.
3. **Reduction to one generator** — NP-completeness and the equivalence between `P = NP` and membership of an NP-complete language in `P`.
4. **Rigid instances** — coverage, rigidity, admissibility, and `NoRigid`.
5. **Main equivalence** — the relationship between `P`, finite coverage, and `P = NP`.
6. **Infinite-family distinction** — definitions for infinite families and a note about what the current model does not establish.
7. **Summary** — a concise statement of the formalized conclusions and their scope.

## Assumptions and interpretation

The results are conditional on the fields of `CModel`. These fields package the complexity theory that a concrete implementation would need to supply, including:

- the predicates `P` and `NP`;
- polynomial-time many-one reducibility;
- a canonical SAT language and its NP-completeness;
- preservation of membership in `P` under reductions;
- the characterization `P_iff_total`, identifying membership in `P` with the existence of a total, sound, polynomial-time solver; and
- the finite-family aggregation principle `P_of_cover`.

These are assumptions of the abstract model in this file, not theorems derived from a concrete machine semantics here. In particular, `P_iff_total`, `sat_hard`, and `P_of_cover` carry substantive mathematical content and must be justified when `CModel` is instantiated for a specific model of computation.

### A point to make precise in a concrete model

The intended finite-family argument is that finitely many polynomial-time partial solvers can be combined into one total polynomial-time solver when their answer regions collectively cover the input space. For this construction to be valid operationally, the meaning of `PolyPartial` must control the running time of an abstention as well as the running time of an answer — for example, each solver must halt with either `some b` or `none` within a polynomial bound.

A promise only that a solver runs in polynomial time *when it answers* would not, by itself, guarantee that trying the solvers in sequence terminates: a solver could fail to answer by running forever. The current structure places the aggregation conclusion in `P_of_cover`; a concrete development should define the runtime semantics precisely and prove that field rather than leave it as an unexplained assumption.

## Why the families are finite

`NoRigid` quantifies over `List Solver`, so its covering family is finite. This matters because a fixed finite collection can, under suitable runtime guarantees, be combined with bounded overhead into one polynomial-time procedure.

The file introduces `InfiniteFamily` and `InfiniteCover` for comparison, but it does **not** prove an infinite-cover theorem or construct a counterexample to one. The declaration

```lean
theorem infinite_cover_not_forced_to_P : True := trivial
```

is deliberately only a trivial placeholder. It records that the current `CModel` has no infinite-family aggregation principle; it should not be read as a proof that an infinite cover fails to imply membership in `P` in every concrete setting.

## What this formalization does — and does not — establish

**It establishes, relative to `CModel`:**

- the reduction from `P = NP` to membership of SAT (or another NP-complete language) in `P`;
- the equivalence between membership in `P` and finite admissible coverage;
- the equivalent rigid-instance formulation of both `P = NP` and `P ≠ NP`.

**It does not establish:**

- `P = NP` or `P ≠ NP`;
- the existence of a finite admissible family covering all SAT instances;
- the existence of an input rigid for every finite admissible SAT family;
- a concrete implementation of `CModel`;
- a new algorithm for SAT, a lower bound, or a resolution of known complexity-theoretic barriers.

The `NoRigid` proposition is the named open content. It is defined and used in equivalences, but it is not asserted as a theorem.

## Building

The source is intended to use Lean 4 without Mathlib. **Compilation has been verified**:

```bash
lean PnP.lean
```

Or, from a Lean project configured with Lake:

```bash
lake env lean PnP.lean
```

Use the Lean version specified by the repository's `lean-toolchain` file, if one is present. Any compiler or tactic errors should be resolved and recorded before treating the formalization as build-verified.

## Suggested next steps

1. **Instantiate `CModel`.** Define the language encoding, machine model, polynomial-time predicates, and reductions explicitly.
2. **Make partial-runtime semantics precise.** Require a polynomial bound for both answers and abstentions, then prove the finite aggregation result.
3. **Prove the model fields.** In particular, derive `P_iff_total` and `P_of_cover` from the chosen machine semantics, and provide the Cook–Levin reduction results.
4. **Compile and audit.** Verify the file with the target Lean toolchain and inspect all assumptions in any eventual concrete instance.
5. **Attack the open statement.** A separation result would need to prove that every finite admissible family for SAT leaves a rigid input. A collapse result would need to exhibit one finite admissible family that covers every SAT input.

## Author

**Auro Zera** — original architecture and subsequent improvements.

---

*The goal of this formalization is to make the finite-covering structure of the P vs NP question explicit and machine-checkable. Its value is in the precision of the reduction framework; the unresolved mathematical burden remains in the assumptions and, ultimately, in the open `NoRigid` statement.*
