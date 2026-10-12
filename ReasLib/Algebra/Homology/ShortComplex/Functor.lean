/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Structure on functors of short complexes

This leaf records the zero-morphism and additive structure inherited by the
short-complex functor induced from an ambient functor.  It is independent of
any particular abelian category, tensor construction, or source presentation.
-/

@[expose] public section

universe vC vD uC uD

namespace CategoryTheory.Functor

section ZeroMorphisms

variable {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]

/-- The functor on short complexes induced by a zero-morphism-preserving functor also preserves
zero morphisms. -/
@[stacks 058N "zero-morphism preservation for the short-complex functor"]
instance mapShortComplex_preservesZeroMorphisms (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.mapShortComplex.PreservesZeroMorphisms := sorry

end ZeroMorphisms

section Additive

variable {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D]

/-- The functor on short complexes induced by an additive functor is additive. -/
@[stacks 058N "additivity of the short-complex functor"]
instance mapShortComplex_additive (F : C ⥤ D) [F.Additive] :
    F.mapShortComplex.Additive := sorry

end Additive

section Checks

variable {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

end Checks

section AdditiveChecks

variable {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]

end AdditiveChecks

end CategoryTheory.Functor
