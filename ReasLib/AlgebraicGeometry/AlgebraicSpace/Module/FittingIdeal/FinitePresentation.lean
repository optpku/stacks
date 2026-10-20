module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.FinitePresentation

/-!
# Finite type of Fitting ideals on algebraic spaces

The Fitting ideals of a finitely presented module on an algebraic space are of
finite type as modules over its structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting ideal of a finitely presented `𝒪_X`-module is of finite type as
an `𝒪_X`-module. -/
instance instIsFiniteType_fittingIdealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ) :
    (fittingIdealSheaf F r : X.Modules).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
