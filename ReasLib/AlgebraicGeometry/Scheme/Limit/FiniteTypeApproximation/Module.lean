module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- An affine finitely presented morphism and a finitely presented module on its source admit
a finite-type approximation diagram carrying a coherent module whose pullback recovers the
original module. -/
theorem exists_isPullback_with_coherent
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (ℱ₀ : D.W.Modules) (_ : ℱ₀.IsCoherent),
      IsPullback D.toW f D.toSi π ∧
        Nonempty ((Scheme.Modules.pullback D.toW).obj ℱ₀ ≅ ℱ) := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
