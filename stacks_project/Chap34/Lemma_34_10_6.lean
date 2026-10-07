module

import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Refinement
import StacksCheckRecall

universe u

/- Lemma 34.10.6 (1): a finite affine family over an affine scheme is a
standard `V` covering if and only if it admits a refinement by a standard `V`
covering. -/
@[stacks 0ETG] #check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_iff_exists_refinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (family : AlgebraicGeometry.AffineFamilyOver T),
        AlgebraicGeometry.AffineFamilyOver.IsStandardVCover family ↔
          ∃ (refining : AlgebraicGeometry.AffineFamilyOver T)
            (refinement : AlgebraicGeometry.AffineFamilyOver.Refinement refining family),
              AlgebraicGeometry.AffineFamilyOver.IsStandardVCover refining)

/- Lemma 34.10.6 (2): a finite affine family over an affine scheme is a
standard `V` covering if and only if the induced coproduct morphism, regarded
as a singleton affine family, is a standard `V` covering. -/
@[stacks 0ETG] #check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_iff_coproductSingleton :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (family : AlgebraicGeometry.AffineFamilyOver T),
        AlgebraicGeometry.AffineFamilyOver.IsStandardVCover family ↔
          AlgebraicGeometry.AffineFamilyOver.IsStandardVCover
            (AlgebraicGeometry.AffineFamilyOver.coproductSingleton family))
