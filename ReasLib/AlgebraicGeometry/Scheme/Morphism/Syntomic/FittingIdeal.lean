/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.RelativeDimension

@[expose] public section

open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a syntomic morphism of relative dimension one, the zeroth Fitting ideal sheaf of
relative differentials is the zero ideal sheaf. -/
theorem fittingIdealSheaf_differentials_zero_eq_bot
    {X S : Scheme.{u}} (f : X ⟶ S) [SyntomicOfRelativeDimension f 1] :
    Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0 = ⊥ := sorry

/-- For a syntomic morphism of relative dimension one, the support of the first Fitting ideal
sheaf of relative differentials is the complement of the smooth locus. -/
theorem fittingIdealSheaf_differentials_one_support_eq_compl_smoothLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [SyntomicOfRelativeDimension f 1] :
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).support : Set X) =
      (f.smoothLocus : Set X)ᶜ := sorry

end AlgebraicGeometry.Scheme.Hom
