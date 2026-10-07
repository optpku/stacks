module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.DiscreteValuationRing

open AlgebraicGeometry

universe u

/- Lemma 31.15.4: if `X` is a Noetherian scheme and `D ⊆ X` is an integral closed subscheme
which is also an effective Cartier divisor, then the local ring of `X` at the generic point of
`D` is a discrete valuation ring. -/
@[stacks 0AG9] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.instIsDiscreteValuationRingAmbientStalkAtGenericPoint :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsIntegral D.subscheme],
      @IsDiscreteValuationRing
        (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) inferInstance
        (AlgebraicGeometry.Scheme.IdealSheafData.instIsDomainAmbientStalkAtGenericPoint D))
