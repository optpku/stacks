module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.RelativeDimension
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 35.23.27: for fixed `d : ℕ`, the property that a scheme morphism is
locally of finite type of relative dimension `d` is fpqc local on the base. -/
@[stacks 02VJ] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimension.isLocalAtTargetFpqc :
    ∀ d : ℕ,
      MorphismProperty.IsLocalAtTarget
        ((fun _ _ f ↦ AlgebraicGeometry.Scheme.Hom.RelativeDimension f d) :
          MorphismProperty AlgebraicGeometry.Scheme.{u})
        AlgebraicGeometry.Scheme.fpqcPrecoverage)
