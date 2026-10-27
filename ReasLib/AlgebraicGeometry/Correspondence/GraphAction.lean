/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Transpose.Graph
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

private theorem graphAction_capFamily_ext {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {s : ℤ} {alpha beta : BivariantClass (fun _ ↦ 0) f s}
    (h : @alpha.cap = @beta.cap) : alpha = beta := by
  cases alpha
  cases beta
  cases h
  rfl

/-- Integral operational Chow pullback along a morphism, obtained by restriction along
the cartesian identity square. -/
def integralCohomologyPullback
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) (s : ℤ) :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
      (BivariantClass (fun _ ↦ 0) (𝟙 Y) s)
      (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
      (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s).toAddCommMonoid
      (@AddCommGroup.toIntModule _
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s))
      (@AddCommGroup.toIntModule _
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s)) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s
  ({ toFun := fun alpha ↦
       BivariantClass.restrict (fun _ ↦ 0) f (𝟙 Y) f
         IsPullback.of_id_snd s alpha
     map_add' := by
       intro alpha beta
       apply graphAction_capFamily_ext
       rfl
     map_smul' := by
       intro n alpha
       letI := sourceGroup
       letI := targetGroup
       let restrictHom : BivariantClass (fun _ ↦ 0) (𝟙 X) s →+
           BivariantClass (fun _ ↦ 0) (𝟙 Y) s :=
         AddMonoidHom.mk'
           (BivariantClass.restrict (fun _ ↦ 0) f (𝟙 Y) f IsPullback.of_id_snd s)
           (fun alpha beta ↦ by
             apply graphAction_capFamily_ext
             rfl)
       exact map_zsmul restrictHom n alpha } :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
      (BivariantClass (fun _ ↦ 0) (𝟙 Y) s)
      sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
      (@AddCommGroup.toIntModule _ sourceGroup)
      (@AddCommGroup.toIntModule _ targetGroup))

/-- Integral operational Chow pullback is bivariant restriction along the identity square. -/
theorem integralCohomologyPullback_apply
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) (s : ℤ)
    (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) :
    integralCohomologyPullback f s alpha =
      BivariantClass.restrict (fun _ ↦ 0) f (𝟙 Y) f
        IsPullback.of_id_snd s alpha := rfl

/-- Rational operational Chow pullback along a morphism. -/
noncomputable def cohomologyPullback
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) (s : ℤ) :
    RationalChowCohomology X s →ₗ[ℚ] RationalChowCohomology Y s :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s
  @LinearMap.baseChange ℤ ℚ
    (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
    (BivariantClass (fun _ ↦ 0) (𝟙 Y) s) inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ sourceGroup)
    (@AddCommGroup.toIntModule _ targetGroup) (integralCohomologyPullback f s)

/-- Rational operational Chow pullback on a pure tensor is scalar extension of bivariant restriction. -/
theorem cohomologyPullback_tmul
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) (s : ℤ) (a : ℚ)
    (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) :
    cohomologyPullback f s
        (@TensorProduct.tmul ℤ inferInstance ℚ
          (BivariantClass (fun _ ↦ 0) (𝟙 X) s) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _
            (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s)) a alpha) =
      @TensorProduct.tmul ℤ inferInstance ℚ
        (BivariantClass (fun _ ↦ 0) (𝟙 Y) s) inferInstance
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s).toAddCommMonoid
        inferInstance (@AddCommGroup.toIntModule _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) s)) a
        (integralCohomologyPullback f s alpha) := rfl

/-- Rational proper pushforward on Chow homology. -/
noncomputable def homologyPushforward
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) [IsProper f.left] (n : ℤ) :
    RationalChowHomology Y n →ₗ[ℚ] RationalChowHomology X n :=
  (ChowGroup.map (fun _ ↦ 0) Y X f n).toIntLinearMap.baseChange ℚ

/-- Rational proper pushforward on a pure tensor is scalar extension of `ChowGroup.map`. -/
theorem homologyPushforward_tmul
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : Y ⟶ X) [IsProper f.left] (n : ℤ)
    (a : ℚ) (alpha : RelativeChow (fun _ ↦ 0) Y n) :
    homologyPushforward f n (a ⊗ₜ[ℤ] alpha) =
      a ⊗ₜ[ℤ] ChowGroup.map (fun _ ↦ 0) Y X f n alpha := rfl

/-- Integral Poincare duality sends an operational class to its cap product with the fundamental class. -/
noncomputable def integralPoincareDuality
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (s : ℤ) :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
      (RelativeChow (fun _ ↦ 0) X ((d : ℤ) - s))
      (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
      inferInstance
      (@AddCommGroup.toIntModule _
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s)) inferInstance :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
      (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing
  let hX : IsLocallyNoetherian X.left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance hBase
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  ({ toFun := fun alpha ↦
       alpha.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst d
         (@chowClass X.left hX
           (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d
           (@CycleGroup.fundamental X.left hX
             (X.hom.relativeDimensionFunction (fun _ ↦ 0)) d))
     map_add' := by
       intro alpha beta
       rfl
     map_smul' := by
       intro n alpha
       letI := sourceGroup
       let capHom : BivariantClass (fun _ ↦ 0) (𝟙 X) s →+
           RelativeChow (fun _ ↦ 0) X ((d : ℤ) - s) :=
         AddMonoidHom.mk'
           (fun alpha ↦ alpha.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst d
             (@chowClass X.left hX
               (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d
               (@CycleGroup.fundamental X.left hX
                 (X.hom.relativeDimensionFunction (fun _ ↦ 0)) d)))
           (fun alpha beta ↦ rfl)
       exact map_zsmul capHom n alpha } :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
      (RelativeChow (fun _ ↦ 0) X ((d : ℤ) - s))
      sourceGroup.toAddCommMonoid inferInstance
      (@AddCommGroup.toIntModule _ sourceGroup) inferInstance)

/-- Integral Poincare duality evaluates an operational class on the fundamental class. -/
theorem integralPoincareDuality_apply
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (s : ℤ) (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) :
    integralPoincareDuality X d s alpha =
      let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
        @instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing
      let hX : IsLocallyNoetherian X.left :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance hBase
      alpha.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst d
        (@chowClass X.left hX (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d
          (@CycleGroup.fundamental X.left hX
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) d)) := rfl

/-- Rational Poincare duality is scalar extension of cap product with the fundamental class. -/
noncomputable def poincareDuality
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (s : ℤ) :
    RationalChowCohomology X s →ₗ[ℚ]
      RationalChowHomology X ((d : ℤ) - s) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  @LinearMap.baseChange ℤ ℚ
    (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
    (RelativeChow (fun _ ↦ 0) X ((d : ℤ) - s)) inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule _ sourceGroup) inferInstance
    (integralPoincareDuality X d s)

/-- Rational Poincare duality on a pure tensor is the rationalized cap product. -/
theorem poincareDuality_tmul
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (s : ℤ) (a : ℚ)
    (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) :
    poincareDuality X d s
        (@TensorProduct.tmul ℤ inferInstance ℚ
          (BivariantClass (fun _ ↦ 0) (𝟙 X) s) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _
            (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s)) a alpha) =
      a ⊗ₜ[ℤ] integralPoincareDuality X d s alpha := rfl

/-- For a smooth equidimensional scheme of dimension `d`, capping with its fundamental class is bijective. -/
theorem poincareDuality_bijective
    (X : SchemeOverField k) [Smooth X.hom] [EquidimensionalSpace X.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (s : ℤ) :
    Function.Bijective (poincareDuality X d s) := sorry

/-- The grading identification used after applying Poincare duality to transposed-graph pushforward. -/
theorem transposedPushforwardDegree (d e : ℕ) (s : ℤ) :
    (d : ℤ) - (s + ((d : ℤ) - (e : ℤ) + 0)) = (e : ℤ) - s := by
  omega

/-- The grading identification placing a Poincare-dual class in the input of transposed-graph pullback. -/
theorem transposedPullbackInputDegree (d : ℕ) (s : ℤ) :
    (d : ℤ) - s = -(s - (d : ℤ)) := by
  omega

/-- The grading identification used after transposed-graph pullback. -/
theorem transposedPullbackOutputDegree (d e : ℕ) (s : ℤ) :
    -((d : ℤ) - (e : ℤ) + 0 + (s - (d : ℤ))) = (e : ℤ) - s := by
  omega

/-- The degree-zero graph correspondence acts on rational operational Chow cohomology as Gysin pullback. -/
theorem pushforward_graph
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowCohomology X s) :
    castCohomologyDegree (Int.add_zero s)
        (pushforward X Y 0 s (rationalGraph f) alpha) =
      cohomologyPullback f s alpha := sorry

/-- Pullback by the degree-zero graph correspondence acts on rational Chow homology as proper pushforward. -/
theorem pullback_graph
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowHomology Y (-s)) :
    castHomologyDegree (congrArg Neg.neg (Int.zero_add s))
        (pullback X Y 0 s (rationalGraph f) alpha) =
      homologyPushforward f (-s) alpha := sorry

/-- Under Poincare duality, pushforward by the transposed graph agrees with proper pushforward. -/
theorem pushforward_transposedGraph
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] [Smooth Y.hom] [Projective Y.hom]
    [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
    (f : Y ⟶ X) (s : ℤ) (alpha : RationalChowCohomology Y s) :
    castHomologyDegree (transposedPushforwardDegree d e s)
        (poincareDuality X d (s + ((d : ℤ) - (e : ℤ) + 0))
          (pushforward Y X ((d : ℤ) - (e : ℤ) + 0) s
            (transposedGraph X Y d e hXdim hYdim f) alpha)) =
      homologyPushforward f ((e : ℤ) - s) (poincareDuality Y e s alpha) := sorry

/-- Under Poincare duality, pullback by the transposed graph agrees with Gysin pullback. -/
theorem pullback_transposedGraph
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] [Smooth Y.hom] [Projective Y.hom]
    [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
    (f : Y ⟶ X) (s : ℤ) (alpha : RationalChowCohomology X s) :
    castHomologyDegree (transposedPullbackOutputDegree d e s)
        (pullback Y X ((d : ℤ) - (e : ℤ) + 0) (s - (d : ℤ))
          (transposedGraph X Y d e hXdim hYdim f)
          (castHomologyDegree (transposedPullbackInputDegree d s)
            (poincareDuality X d s alpha))) =
      poincareDuality Y e s (cohomologyPullback f s alpha) := sorry

end AlgebraicGeometry.Correspondence
