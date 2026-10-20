module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiFinite
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 35.23.26 (1): the property that a scheme morphism is locally quasi-finite in the
finite-type sense is fpqc local on the base. -/
@[stacks 02VI] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.23.26 (2): the property that a scheme morphism is quasi-finite is fpqc local
on the base. -/
@[stacks 02VI] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.QuasiFinite :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
