module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation

/-!
# Gluing categories for finitely presented modules

This leaf packages the categorical pullback describing a pair of finitely
presented modules whose restrictions agree over a specified open subscheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The category of gluing data for finitely presented modules on an open `U`, on a scheme `T`,
and on an open `V ⊆ T`, identified after pullback along `V.toScheme ⟶ U.toScheme`. -/
abbrev finitePresentationModuleGluingCategory
    {S T : Scheme.{u}} (U : S.Opens) (V : T.Opens)
    (toU : V.toScheme ⟶ U.toScheme) : Type (u + 1) :=
  CategoricalPullback
    (FinitePresentationModules.inclusion U.toScheme ⋙ Scheme.Modules.pullback toU)
    (FinitePresentationModules.inclusion T ⋙ Scheme.Modules.pullback V.ι)

end AlgebraicGeometry
