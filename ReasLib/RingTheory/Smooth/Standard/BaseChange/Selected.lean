/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.Jacobian.BaseChange
public import ReasLib.RingTheory.Extension.Presentation.RelationIdeal.BaseChange
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for selected standard data

This leaf owns base-change results for embedding-indexed presentation data and
for the presentation-independent standard-element predicates.
-/

@[expose] public section

open scoped TensorProduct

universe u v w t x

section

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

namespace Algebra.Presentation.IsElementaryFor

variable {ι : Type t} {σ : Type x} {c : ℕ}

/-- Fixed-presentation elementary data is preserved by coefficient base change. -/
@[stacks 07CC "elementary standard data under base change"]
theorem baseChange
    {P : Presentation R A ι σ} {a : A}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (h : P.IsElementaryFor a cols rows) :
    (P.baseChange R').IsElementaryFor
      ((1 : R') ⊗ₜ[R] a) cols rows := sorry

end Algebra.Presentation.IsElementaryFor

namespace Algebra.Presentation.IsStrictlyFor

variable {ι : Type t} {σ : Type x} {c : ℕ}

/-- Fixed-presentation strict data is preserved by coefficient base change. -/
@[stacks 07CC "strict standard data under base change"]
theorem baseChange
    {P : Presentation R A ι σ} {a : A} {rows : Fin c ↪ σ}
    (h : P.IsStrictlyFor a rows) :
    (P.baseChange R').IsStrictlyFor
      ((1 : R') ⊗ₜ[R] a) rows := sorry

end Algebra.Presentation.IsStrictlyFor

namespace Algebra

/-- An elementary standard element remains elementary standard after scalar extension. -/
@[stacks 07CC "elementary standard elements under base change"]
theorem IsElementaryStandard.baseChange
    {a : A} (ha : IsElementaryStandard R a) :
    IsElementaryStandard R' ((1 : R') ⊗ₜ[R] a) := sorry

/-- A strictly standard element remains strictly standard after scalar extension. -/
@[stacks 07CC "strictly standard elements under base change"]
theorem IsStrictlyStandard.baseChange
    {a : A} (ha : IsStrictlyStandard R a) :
    IsStrictlyStandard R' ((1 : R') ⊗ₜ[R] a) := sorry

end Algebra

end
