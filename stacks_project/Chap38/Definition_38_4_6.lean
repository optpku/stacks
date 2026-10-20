module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Definition 38.4.6 -/
@[stacks 05H9] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking :
    {S : Scheme.{u}} → {X : CategoryTheory.Over S} → {ℱ : X.left.Modules} →
      [LocallyOfFiniteType X.hom] → [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
      {x : X.left} →
        (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint X ℱ x) →
          Type (u + 1))
