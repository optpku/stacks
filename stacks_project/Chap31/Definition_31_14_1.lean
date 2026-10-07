module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Definition 31.14.1 (1): for an effective Cartier divisor `D` on `X`, the associated sheaf
`𝒪_X(D)` is the internal-Hom dual of its ideal sheaf. -/
@[stacks 01WX] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      SheafOfModules X.ringCatSheaf)

/- Definition 31.14.1 (2): the canonical section of `𝒪_X(D)` corresponds to the inclusion of
the ideal sheaf of `D` into the structure sheaf. -/
@[stacks 01WX] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.canonicalSection :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      (AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf D).sections)

/- Definition 31.14.1 (3): the negative-divisor sheaf `𝒪_X(-D)` is the ideal sheaf of `D`. -/
@[stacks 01WX] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.negSheaf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      SheafOfModules X.ringCatSheaf)

/- Definition 31.14.1 (4): for effective Cartier divisors `D` and `D'`, the difference sheaf
`𝒪_X(D-D')` is `𝒪_X(D) ⊗ 𝒪_X(-D')`. -/
@[stacks 01WX] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.differenceSheaf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (D D' : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι],
      SheafOfModules X.ringCatSheaf)

/- Evaluation of an invertible ideal sheaf against its associated sheaf is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.effectiveCartierDivisorAssociatedSheaf_evaluationIso :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
      (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
        SheafOfModules X.ringCatSheaf))
      [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))],
      IsIso (AlgebraicGeometry.Scheme.effectiveCartierDivisorEvaluationHom
        (X := X) I))

/- The sheaf associated to an invertible ideal sheaf is invertible. -/
#check
  (AlgebraicGeometry.Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
      (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
        SheafOfModules X.ringCatSheaf))
      [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))],
      AlgebraicGeometry.Scheme.Modules.Invertible
        (AlgebraicGeometry.Scheme.effectiveCartierDivisorAssociatedSheaf I))
