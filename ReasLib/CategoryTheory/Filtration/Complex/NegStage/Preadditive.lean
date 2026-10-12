/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage
public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of negative filtration stages

The negative-stage facade is a specialization of the generic antitone
stage-sequence functor.  This file registers the inherited additive
structure at the specialized name so downstream code can import one small
support leaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The negative-stage diagram functor is additive in the filtered complex. -/
@[stacks 0D8Z]
noncomputable instance functor_additive :
    (functor (A := A)).Additive := sorry

#synth (functor (A := A)).Additive

end CategoryTheory.FilteredComplex.NegStage
