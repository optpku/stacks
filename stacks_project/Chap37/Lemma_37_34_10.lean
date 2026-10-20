module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Syntomic
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.10: a standard syntomic morphism `f : X ⟶ S` between affine schemes is
obtained from a standard syntomic finite-type morphism `D.toSi : D.W ⟶ S₀` between affine
schemes by a cartesian square, where `S₀` is of finite type over `Spec ℤ`. -/
@[stacks 05FK] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_of_standardSyntomic :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) (_ : StandardSyntomic f),
      ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
        (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
        (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
        (_ : Scheme.Hom.FiniteType D.toSi),
        IsPullback D.toW f D.toSi π ∧ StandardSyntomic D.toSi)

end AlgebraicGeometry.FiniteTypeApproximationDiagram
