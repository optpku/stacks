module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Descent

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.34.2: For an fppf hypercovering augmentation, pullback of quasi-coherent
modules is an equivalence with the canonical augmentation pushforward as quasi-inverse. -/
@[stacks 0DHD] #check (AlgebraicGeometry.AlgebraicSpace.Simplicial.qcohDescent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X),
    IsFppfHypercovering a →
      ((spacesQuasiCoherentModuleProperty X).FullSubcategory ≌ QCoh U))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.qcohDescent_functor :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    (qcohDescent a ha).functor = QCoh.pullback a)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.qcohDescent_inverse :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    (qcohDescent a ha).inverse = QCoh.pushforward a ha)
