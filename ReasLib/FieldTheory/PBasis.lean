/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.FieldTheory.Frobenius.Compositum
import Mathlib.Tactic.CrossRefAttribute

/-!
# p-bases

@stack 07P1

The p-basis definitions are kept in the `FieldExtension.PBasis` namespace.  The public owner uses
the shared Frobenius subfield together with named monomial and compositum constructions; the chapter
keeps its older root names as thin compatibility views.  No caret notation is exported here, since
several field-theory scopes already use similar visual notation.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace FieldExtension.PBasis

open FieldExtension.Frobenius

/-- The restricted monomial indexed by a finitely supported `Fin p`-valued exponent. -/
@[stacks 07P1 "restricted p-monomial"]
abbrev monomial (p : ℕ) {K : Type v} [CommMonoidWithZero K] [NeZero p] {ι : Type w}
    (x : ι → K) : (ι →₀ Fin p) → K :=
  fun e ↦ e.support.prod fun i ↦ x i ^ (e i : ℕ)

section Field

variable (p : ℕ) (k : Type u) {K : Type v} {ι : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [Fact p.Prime] [CharP K p]

/-- A family is p-independent when its restricted monomials are linearly independent over the
compositum of the base field and the `p`-th powers. -/
@[stacks 07P1 "p-independence"]
abbrev IsIndependent (x : ι → K) : Prop :=
  LinearIndependent (compositum p k K) (monomial p x)

/-- A family is a p-basis when its restricted monomials are independent and it generates `K` over
the p-power compositum. -/
@[stacks 07P1 "p-basis"]
def IsBasis (x : ι → K) : Prop :=
  IsIndependent p k x ∧
    IntermediateField.adjoin (compositum p k K) (Set.range x) = ⊤

/-- The p-basis predicate is equivalently the linear-basis condition on the restricted monomials. -/
@[stacks 07P1 "p-basis monomial span characterization"]
theorem isBasis_iff_monomial_span (x : ι → K) :
    IsBasis p k x ↔
      LinearIndependent (compositum p k K) (monomial p x) ∧
        Submodule.span (compositum p k K) (Set.range (monomial p x)) = ⊤ := sorry
/- Proof strategy: compare field generation with module span of the restricted monomials using
the standard p-power basis criterion for purely inseparable extensions. -/

end Field

namespace IsBasis

section Field

variable {p : ℕ} {k : Type u} {K : Type v} {ι : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [Fact p.Prime] [CharP K p]

/-- The linear-independence component of a p-basis. -/
@[stacks 07P1 "p-basis independence component"]
theorem independent {x : ι → K} (h : IsBasis p k x) :
    IsIndependent p k x := h.1
/- Proof strategy: project the `IsIndependent` component of the defining conjunction. -/

/-- The generating component of a p-basis. -/
@[stacks 07P1 "p-basis generation component"]
theorem adjoin_eq_top {x : ι → K} (h : IsBasis p k x) :
    IntermediateField.adjoin (compositum p k K) (Set.range x) = ⊤ := h.2
/- Proof strategy: project the second component of the defining conjunction. -/

end Field

end IsBasis

end FieldExtension.PBasis
