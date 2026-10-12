/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- An affine finitely presented morphism and a finitely presented module on its source that is
flat over the base admit a finite-type approximation diagram carrying a coherent module flat over
the finite-stage base, whose pullback recovers the original module. -/
theorem exists_isPullback_with_coherent_flatOver
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (ℱ₀ : D.W.Modules) (_ : ℱ₀.IsCoherent)
      (_ : SheafOfModules.IsFlatOver ℱ₀ D.toSi.toShHom),
      IsPullback D.toW f D.toSi π ∧
        Nonempty ((Scheme.Modules.pullback D.toW).obj ℱ₀ ≅ ℱ) := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
