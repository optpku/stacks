module

public import ReasLib.AlgebraicGeometry.ChowGroup.FactorSwap
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.LinearAlgebra.BilinearMap
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The integral Chow-group realization of degree-`r` correspondences from `X` to an
equidimensional target of dimension `e`. -/
abbrev IntegralChowRealization (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (e : ℕ) (r : ℤ) : Type u :=
  @ChowGroup (X ⨯ Y).left
    (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
    ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance ((e : ℤ) - r)

/-- The rational Chow-group realization of degree-`r` correspondences from `X` to an
equidimensional target of dimension `e`. -/
abbrev RationalChowRealization (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (e : ℕ) (r : ℤ) : Type u :=
  ℚ ⊗[ℤ] IntegralChowRealization X Y e r

/-- Realize an integral correspondence by applying it to the fundamental class of its
equidimensional target. -/
noncomputable def integralRealizationMap (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (e : ℕ) (r : ℤ) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  @AddMonoidHom.mk (Integral X Y r) (IntegralChowRealization X Y e r)
    sourceGroup.toAddZero inferInstance
    (@ZeroHom.mk _ _ sourceGroup.toZero inferInstance
      (fun c ↦ c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y)
        IsPullback.of_id_fst e
        (@chowClass Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance e
          (@CycleGroup.fundamental Y.left
            (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) e))) sorry) sorry

/-- The chosen inverse to realization, characterized by the two-sided specifications below. -/
noncomputable def integralRealizationInverse (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (e : ℕ) (r : ℤ) :=
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  @AddMonoidHom.mk (IntegralChowRealization X Y e r) (Integral X Y r)
    inferInstance targetGroup.toAddZero
    (@ZeroHom.mk _ _ inferInstance targetGroup.toZero
      (Function.invFun (integralRealizationMap X Y e r)) sorry) sorry

/-- Applying realization after its chosen inverse recovers the given Chow class when the
target is smooth and equidimensional of dimension `e`. -/
theorem integralRealizationInverse_spec (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ)
    (c : IntegralChowRealization X Y e r) :
    integralRealizationMap X Y e r (integralRealizationInverse X Y e r c) = c := sorry

/-- An integral correspondence is recovered from its Chow realization when the target is
smooth and equidimensional. -/
theorem integralRealizationInverse_apply (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ)
    (c : Integral X Y r) :
    integralRealizationInverse X Y e r (integralRealizationMap X Y e r c) = c := sorry

/-- Capping with the fundamental class identifies integral correspondences with their
Chow-group realization when the target is smooth and equidimensional. -/
noncomputable def integralRealizationEquiv (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  @AddEquiv.mk (Integral X Y r) (IntegralChowRealization X Y e r)
    sourceGroup.toAdd inferInstance
    (@Equiv.mk _ _ (integralRealizationMap X Y e r)
      (integralRealizationInverse X Y e r)
      (integralRealizationInverse_apply X Y e hYdim r)
      (integralRealizationInverse_spec X Y e hYdim r))
    (integralRealizationMap X Y e r).map_add

/-- Scalar extension of integral realization gives the rational realization map. -/
noncomputable def rationalRealizationMap (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ) :
    Rational X Y r →ₗ[ℚ] RationalChowRealization X Y e r :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let integral := integralRealizationEquiv X Y e hYdim r
  let forwardMap := (@AddEquiv.toIntLinearEquiv _ _ sourceGroup inferInstance
    (@AddCommGroup.toIntModule _ sourceGroup) inferInstance integral).toLinearMap
  forwardMap.baseChange ℚ

/-- Scalar extension of the integral realization equivalence gives the rational
correspondence-to-Chow comparison. -/
noncomputable def realizationEquiv (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ) :
    Rational X Y r ≃ₗ[ℚ] RationalChowRealization X Y e r :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let integral := integralRealizationEquiv X Y e hYdim r
  let inverseEquiv := integral.symm
  let inverseMap := (@AddEquiv.toIntLinearEquiv _ _ inferInstance sourceGroup
    inferInstance (@AddCommGroup.toIntModule _ sourceGroup) inverseEquiv).toLinearMap
  { rationalRealizationMap X Y e hYdim r with
    invFun := inverseMap.baseChange ℚ
    left_inv := sorry
    right_inv := sorry }

/-- Rational realization is scalar extension of capping integral correspondences with the
fundamental class. -/
theorem realizationEquiv_apply (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ)
    (c : Rational X Y r) :
    realizationEquiv X Y e hYdim r c =
      rationalRealizationMap X Y e hYdim r c := sorry

/-- The grading identity underlying transpose of a degree-`r` correspondence. -/
theorem transposeDegree (d e : ℕ) (r : ℤ) :
    (e : ℤ) - r = (d : ℤ) - ((d : ℤ) - (e : ℤ) + r) := sorry

/-- Factor exchange gives the `ℚ`-linear transpose equivalence on the Chow realizations
of `Corr^r(X, Y)` and `Corr^(d - e + r)(Y, X)`. -/
noncomputable def realizationTranspose (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ) :
    RationalChowRealization X Y e r ≃ₗ[ℚ]
      RationalChowRealization Y X d ((d : ℤ) - (e : ℤ) + r) :=
  let integral := (ChowGroup.swapEquiv X Y ((e : ℤ) - r)).trans
    (ChowGroup.degreeEquiv (Y ⨯ X) (transposeDegree d e r))
  { integral.toIntLinearEquiv.toLinearMap.baseChange ℚ with
    invFun := integral.symm.toIntLinearEquiv.toLinearMap.baseChange ℚ
    left_inv := sorry
    right_inv := sorry }

/-- Realization-level transpose is scalar extension of factor exchange followed by grading
transport. -/
theorem realizationTranspose_apply (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ)
    (c : RationalChowRealization X Y e r) :
    realizationTranspose X Y d e hXdim hYdim r c =
      (((ChowGroup.swapEquiv X Y ((e : ℤ) - r)).trans
        (ChowGroup.degreeEquiv (Y ⨯ X) (transposeDegree d e r))).toIntLinearEquiv.toLinearMap.baseChange ℚ) c :=
  sorry

/-- Transpose of rational correspondences, obtained by Chow realization, factor exchange,
and inverse realization. -/
noncomputable def transpose (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ) :
    Rational X Y r ≃ₗ[ℚ] Rational Y X ((d : ℤ) - (e : ℤ) + r) :=
  (realizationEquiv X Y e hYdim r).trans
    ((realizationTranspose X Y d e hXdim hYdim r).trans
      (realizationEquiv Y X d hXdim ((d : ℤ) - (e : ℤ) + r)).symm)

/-- Applying transpose is source realization followed by factor exchange and inverse target
realization. -/
theorem transpose_apply (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (r : ℤ)
    (c : Rational X Y r) :
    transpose X Y d e hXdim hYdim r c =
      (realizationEquiv Y X d hXdim ((d : ℤ) - (e : ℤ) + r)).symm
        (realizationTranspose X Y d e hXdim hYdim r
          (realizationEquiv X Y e hYdim r c)) := sorry

end AlgebraicGeometry.Correspondence
