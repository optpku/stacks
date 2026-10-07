module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Refinement

@[expose] public section

open CategoryTheory

universe u

/- Lemma 34.10.4: a standard `V` covering remains standard after pullback
along a morphism from an affine scheme. -/
@[stacks 0ETE] #check
  (AlgebraicGeometry.AffineFamilyOver.IsStandardVCover.pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}}
      {family : AlgebraicGeometry.AffineFamilyOver T}
      (_ : AlgebraicGeometry.AffineFamilyOver.IsStandardVCover family)
      (g : T' ⟶ T) [AlgebraicGeometry.IsAffine T'],
        AlgebraicGeometry.AffineFamilyOver.IsStandardVCover
          (AlgebraicGeometry.AffineFamilyOver.pullback family g))
