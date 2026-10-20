module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfGlobalSections

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial

/- Lemma 85.33.4. An fppf hypercovering computes bounded-below derived étale
 global sections through the total étale augmentation. -/
@[stacks 0DH8] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaInverseImageComparison_app_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
      IsFppfHypercovering a →
      ∀ K : DerivedCategory.Plus
        (Sheaf (AlgebraicSpace.spacesEtaleTopology X) AddCommGrpCat.{u + 1}),
        IsIso ((rGammaInverseImageComparison a).app K))
