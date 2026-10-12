/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived additive Cech complexes of module sheaves

This file owns the basic passage from the additive Cech complex of a module sheaf to the
unbounded derived category.  It is intentionally independent of maps of ringed spaces and of
comparison morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

/-- The Cech complex of a module sheaf, extended by zero and localized in the unbounded derived
category. -/
@[stacks 01EQ "derived Cech-complex functor", stacks 01FD "derived Cech-complex functor"]
abbrev derivedFunctor {Z : RingedSpace.{u}} {I : Type u}
    (U : I → Opens Z.carrier) : Z.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleCechComplexFunctor U ⋙
    CochainComplex.Plus.extendNat AddCommGrpCat.{u} ⋙
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι

end AlgebraicGeometry.RingedSpace.ModuleCech
