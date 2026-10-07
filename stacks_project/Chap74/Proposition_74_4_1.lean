module

public import stacks_project.Chap74.Proposition_74_4_1_Fpqc
import StacksCheckRecall

@[expose] public section

universe u v

/- Proposition 74.4.1 (1): every quasi-coherent descent datum for an fpqc covering
of algebraic spaces over a scheme is effective. -/
@[stacks 04W8] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.isEffective_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      {ι : Type v} {family : ι → CategoryTheory.Over X},
      AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
        ∀ D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom),
          AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.IsEffective D)

/- Proposition 74.4.1 (2): the canonical functor from quasi-coherent modules to
descent data for an fpqc covering of algebraic spaces is fully faithful. -/
@[stacks 04W8] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor.fullyFaithful_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      {ι : Type v} {family : ι → CategoryTheory.Over X},
      AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
        Nonempty
          (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).FullyFaithful)
