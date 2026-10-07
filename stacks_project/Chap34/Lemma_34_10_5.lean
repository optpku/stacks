module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Refinement

@[expose] public section

universe u

/-!
# Lemma 34.10.5

This chapter entry is a compatibility facade for composition of finite affine
families and standard `V` covers.
-/

#check AlgebraicGeometry.AffineFamilyOver.comp

/- Lemma 34.10.5: a composite of finite affine standard `V` coverings is a
standard `V` covering. -/
@[stacks 0ETF] #check
  (AlgebraicGeometry.AffineFamilyOver.IsStandardVCover.comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}
      {family : AlgebraicGeometry.AffineFamilyOver T} [AlgebraicGeometry.IsAffine T],
        AlgebraicGeometry.AffineFamilyOver.IsStandardVCover family →
          (refining : (i : Fin family.n) →
            AlgebraicGeometry.AffineFamilyOver (family.U i)) →
          (∀ i, AlgebraicGeometry.AffineFamilyOver.IsStandardVCover (refining i)) →
          AlgebraicGeometry.AffineFamilyOver.IsStandardVCover (family.comp refining))
