module

public import stacks_project.Chap74.Lemma_74_3_4_Zariski
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 74.3.4 (1): every quasi-coherent descent datum for a Zariski covering
of algebraic spaces over a scheme is effective. -/
@[stacks 04W6] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.isEffective_of_zariskiCovering :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
      CategoryTheory.Presieve.ofArrows Xᵢ f ∈
          AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage S X →
        ∀ D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f,
          AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.IsEffective D)

/- Lemma 74.3.4 (2): the canonical functor from quasi-coherent modules to
descent data for a Zariski covering of algebraic spaces is fully faithful. -/
@[stacks 04W6] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor.fullyFaithful_of_zariskiCovering :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
      CategoryTheory.Presieve.ofArrows Xᵢ f ∈
          AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage S X →
        Nonempty
          (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor Xᵢ f).FullyFaithful)
