module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 42.21.1 (1): the zero endpoint fiber of an integral projective-line family of
`delta`-dimension `k + 1` that is contained in neither endpoint is an effective Cartier
divisor. -/
@[stacks 02S4] #check
  (AlgebraicGeometry.ProjectiveLineFamily.zeroPullbackDefined :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
      (W : (AlgebraicGeometry.ProjectiveLineFamily.space X).IdealSheafData)
      [IsIntegral W.subscheme]
      (h_dimension :
        (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫
          X.hom).closedSubschemeDeltaDimension delta W = ((k + 1 : ℤ) : EInt))
      (h_zero : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support)
      (h_infinity : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support),
      Scheme.IdealSheafData.pullbackDefined (ProjectiveLine.Relative.zeroDivisor S)
        (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)))

/- Lemma 42.21.1 (2): the infinity endpoint fiber of an integral projective-line family of
`delta`-dimension `k + 1` that is contained in neither endpoint is an effective Cartier
divisor. -/
@[stacks 02S4] #check
  (AlgebraicGeometry.ProjectiveLineFamily.infinityPullbackDefined :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
      (W : (AlgebraicGeometry.ProjectiveLineFamily.space X).IdealSheafData)
      [IsIntegral W.subscheme]
      (h_dimension :
        (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫
          X.hom).closedSubschemeDeltaDimension delta W = ((k + 1 : ℤ) : EInt))
      (h_zero : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support)
      (h_infinity : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support),
      Scheme.IdealSheafData.pullbackDefined (ProjectiveLine.Relative.infinityDivisor S)
        (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)))

/- Lemma 42.21.1 (3): the degree-`k` cycles of the zero and infinity fibers, viewed as
closed subschemes of `X`, are rationally equivalent. -/
@[stacks 02S4] #check
  (AlgebraicGeometry.ProjectiveLineFamily.zeroCycle_rationallyEquivalent_infinityCycle :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
      (W : (AlgebraicGeometry.ProjectiveLineFamily.space X).IdealSheafData)
      [IsIntegral W.subscheme]
      (h_dimension :
        (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫
          X.hom).closedSubschemeDeltaDimension delta W = ((k + 1 : ℤ) : EInt))
      (h_zero : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support)
      (h_infinity : ¬ (W.support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support),
      @RationalEquivalence.RationallyEquivalent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance k
        (AlgebraicGeometry.ProjectiveLineFamily.zeroCycle delta X k W)
        (AlgebraicGeometry.ProjectiveLineFamily.infinityCycle delta X k W))

/- Lemma 42.21.1 (4): the locally finite sum of the zero endpoint cycles minus the infinity
endpoint cycles of a family as above is rationally equivalent to zero. -/
@[stacks 02S4] #check
  (AlgebraicGeometry.ProjectiveLineFamily.boundary_rationallyEquivalent_zero :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
      {I : Type u}
      (W : I → (AlgebraicGeometry.ProjectiveLineFamily.space X).IdealSheafData)
      (h_integral : ∀ i, IsIntegral (W i).subscheme)
      (h_dimension : ∀ i,
        (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫
          X.hom).closedSubschemeDeltaDimension delta (W i) = ((k + 1 : ℤ) : EInt))
      (h_zero : ∀ i, ¬ ((W i).support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support)
      (h_infinity : ∀ i, ¬ ((W i).support :
        Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support)
      (h_local : LocallyFinite fun i ↦
        ((W i).support : Set (AlgebraicGeometry.ProjectiveLineFamily.space X))),
      @RationalEquivalence.RationallyEquivalent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance k
        (AlgebraicGeometry.ProjectiveLineFamily.boundary delta X k W h_local) 0)

/- Lemma 42.21.1 (5): every degree-`k` cycle rationally equivalent to zero is the locally
finite boundary of a family of integral closed subschemes of `X ×ₛ ℙ¹ₛ` of
`delta`-dimension `k + 1`, none contained in an endpoint fiber. -/
@[stacks 02S4] #check
  (AlgebraicGeometry.ProjectiveLineFamily.exists_boundary_eq_of_rationallyEquivalent_zero :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
      (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k)
      (h_alpha : @RationalEquivalence.RationallyEquivalent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance k alpha 0),
      ∃ (I : Type u)
        (W : I → (AlgebraicGeometry.ProjectiveLineFamily.space X).IdealSheafData),
        (∀ i, IsIntegral (W i).subscheme) ∧
        (∀ i, (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫
          X.hom).closedSubschemeDeltaDimension delta (W i) = ((k + 1 : ℤ) : EInt)) ∧
        (∀ i, ¬ ((W i).support :
          Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
            (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
              (ProjectiveLine.Relative.zeroDivisor S).support) ∧
        (∀ i, ¬ ((W i).support :
          Set (AlgebraicGeometry.ProjectiveLineFamily.space X)) ⊆
            (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
              (ProjectiveLine.Relative.infinityDivisor S).support) ∧
        ∃ h_local : LocallyFinite fun i ↦
          ((W i).support : Set (AlgebraicGeometry.ProjectiveLineFamily.space X)),
          alpha = AlgebraicGeometry.ProjectiveLineFamily.boundary delta X k W h_local)

end AlgebraicGeometry
