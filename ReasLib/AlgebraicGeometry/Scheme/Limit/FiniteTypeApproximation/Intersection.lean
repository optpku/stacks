/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- Two affine finite-type approximations of an affine finitely presented scheme morphism,
satisfying base-change-stable properties `P` and `Q` respectively, admit a single affine
finite-type approximation satisfying `P ⊓ Q`. -/
theorem exists_inf_of_isPullback
    (P Q : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    {X S S₁ S₂ : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine S₁] [IsAffine S₂]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (π₁ : S ⟶ S₁) (π₂ : S ⟶ S₂)
    [Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₁)]
    [Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₂)]
    (D₁ : FiniteTypeApproximationDiagram f π₁)
    (D₂ : FiniteTypeApproximationDiagram f π₂)
    [IsAffine D₁.W] [IsAffine D₂.W]
    [Scheme.Hom.FiniteType D₁.toSi] [Scheme.Hom.FiniteType D₂.toSi]
    (hD₁ : IsPullback D₁.toW f D₁.toSi π₁)
    (hD₂ : IsPullback D₂.toW f D₂.toSi π₂)
    (hP : P D₁.toSi) (hQ : Q D₂.toSi) :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π₀ : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D₀ : FiniteTypeApproximationDiagram f π₀) (_ : IsAffine D₀.W)
      (_ : Scheme.Hom.FiniteType D₀.toSi),
      IsPullback D₀.toW f D₀.toSi π₀ ∧ (P ⊓ Q) D₀.toSi := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
