/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Category

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The projection from a fourfold product to its first and third factors. -/
def projection13 (X₁ X₂ Y₁ Y₂ : Category k) :
    (X₁.scheme ⨯ X₂.scheme) ⨯ (Y₁.scheme ⨯ Y₂.scheme) ⟶ X₁.scheme ⨯ Y₁.scheme :=
  Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.fst)
    (Limits.prod.snd ≫ Limits.prod.fst)

/-- The map retaining the first target factor and the second source-target pair. -/
def projection13Target (X₁ X₂ Y₁ Y₂ : Category k) :
    (X₁.scheme ⨯ X₂.scheme) ⨯ (Y₁.scheme ⨯ Y₂.scheme) ⟶
      Y₁.scheme ⨯ (X₂.scheme ⨯ Y₂.scheme) :=
  Limits.prod.lift (Limits.prod.snd ≫ Limits.prod.fst)
    (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.snd)
      (Limits.prod.snd ≫ Limits.prod.snd))

/-- The square defined by the projection to the first and third factors is cartesian. -/
theorem projection13_isPullback (X₁ X₂ Y₁ Y₂ : Category k) :
    IsPullback (projection13 X₁ X₂ Y₁ Y₂).left
      (projection13Target X₁ X₂ Y₁ Y₂).left
      (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme).left
      (Limits.prod.fst : Y₁.scheme ⨯ (X₂.scheme ⨯ Y₂.scheme) ⟶ Y₁.scheme).left := sorry

/-- Pullback of an integral correspondence along the projection to the first and third
factors. -/
def projectionPullback13 (X₁ X₂ Y₁ Y₂ : Category k)
    (c : Integral X₁.scheme Y₁.scheme 0) :
    BivariantClass (fun _ ↦ 0) (projection13Target X₁ X₂ Y₁ Y₂) 0 :=
  BivariantClass.restrict (fun _ ↦ 0) (projection13 X₁ X₂ Y₁ Y₂)
    (projection13Target X₁ X₂ Y₁ Y₂) Limits.prod.fst
    (projection13_isPullback X₁ X₂ Y₁ Y₂) 0 c

/-- The projection from the middle three factors to the second and fourth factors. -/
def projection24 (X₂ Y₁ Y₂ : Category k) :
    Y₁.scheme ⨯ (X₂.scheme ⨯ Y₂.scheme) ⟶ X₂.scheme ⨯ Y₂.scheme :=
  Limits.prod.snd

/-- The map from the middle three factors to the two target factors. -/
def projection24Target (X₂ Y₁ Y₂ : Category k) :
    Y₁.scheme ⨯ (X₂.scheme ⨯ Y₂.scheme) ⟶ Y₁.scheme ⨯ Y₂.scheme :=
  Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd)

/-- The square defined by the projection to the second and fourth factors is cartesian. -/
theorem projection24_isPullback (X₂ Y₁ Y₂ : Category k) :
    IsPullback (projection24 X₂ Y₁ Y₂).left (projection24Target X₂ Y₁ Y₂).left
      (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme).left
      (Limits.prod.snd : Y₁.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme).left := sorry

/-- The second projection from a product is locally of finite type when its first factor is
locally of finite type over the field. -/
instance productSnd_locallyOfFiniteType (Y Z : SchemeOverField k)
    [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (Limits.prod.snd : Y ⨯ Z ⟶ Z).left := sorry

/-- Pullback of an integral correspondence along the projection to the second and fourth
factors. -/
def projectionPullback24 (X₂ Y₁ Y₂ : Category k)
    (c : Integral X₂.scheme Y₂.scheme 0) :
    BivariantClass (fun _ ↦ 0) (projection24Target X₂ Y₁ Y₂) 0 :=
  BivariantClass.restrict (fun _ ↦ 0) (projection24 X₂ Y₁ Y₂)
    (projection24Target X₂ Y₁ Y₂) Limits.prod.snd
    (projection24_isPullback X₂ Y₁ Y₂) 0 c

/-- The two target projections compose to the second projection from the fourfold product. -/
theorem projectionTargets_comp (X₁ X₂ Y₁ Y₂ : Category k) :
    projection13Target X₁ X₂ Y₁ Y₂ ≫ projection24Target X₂ Y₁ Y₂ =
      (Limits.prod.snd :
        (X₁.scheme ⨯ X₂.scheme) ⨯ (Y₁.scheme ⨯ Y₂.scheme) ⟶
          Y₁.scheme ⨯ Y₂.scheme) := sorry

/-- The intersection of two projection pullbacks, regarded as an integral correspondence on
products. -/
def integralIntersection (X₁ X₂ Y₁ Y₂ : Category k)
    (c : Integral X₁.scheme Y₁.scheme 0) (d : Integral X₂.scheme Y₂.scheme 0) :
    Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme 0 :=
  Eq.mp
    (congrArg (fun f ↦ BivariantClass (fun _ ↦ 0) f 0)
      (projectionTargets_comp X₁ X₂ Y₁ Y₂))
    (BivariantClass.comp (fun _ ↦ 0) (projection13Target X₁ X₂ Y₁ Y₂)
      (projection24Target X₂ Y₁ Y₂) (projectionPullback13 X₁ X₂ Y₁ Y₂ c)
      (projectionPullback24 X₂ Y₁ Y₂ d))

/-- Integral projection-pullback/intersection is additive in its second correspondence. -/
theorem integralIntersection_add_right (X₁ X₂ Y₁ Y₂ : Category k)
    (c : Integral X₁.scheme Y₁.scheme 0) (d₁ d₂ : Integral X₂.scheme Y₂.scheme 0) :
    integralIntersection X₁ X₂ Y₁ Y₂ c
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd 0 d₁ d₂) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd 0
        (integralIntersection X₁ X₂ Y₁ Y₂ c d₁)
        (integralIntersection X₁ X₂ Y₁ Y₂ c d₂) := sorry

/-- Integral projection-pullback/intersection respects integer scaling in its second input. -/
theorem integralIntersection_zsmul_right (X₁ X₂ Y₁ Y₂ : Category k)
    (c : Integral X₁.scheme Y₁.scheme 0) (n : ℤ)
    (d : Integral X₂.scheme Y₂.scheme 0) :
    integralIntersection X₁ X₂ Y₁ Y₂ c
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd 0 d n) =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd 0
        (integralIntersection X₁ X₂ Y₁ Y₂ c d) n := sorry

/-- Intersection with a fixed first correspondence, as an explicitly structured
integer-linear map. -/
def integralTensorRight (X₁ X₂ Y₁ Y₂ : Category k)
    (c : Integral X₁.scheme Y₁.scheme 0) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) 0
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
      (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) 0
  ({ toFun := integralIntersection X₁ X₂ Y₁ Y₂ c
     map_add' := integralIntersection_add_right X₁ X₂ Y₁ Y₂ c
     map_smul' := integralIntersection_zsmul_right X₁ X₂ Y₁ Y₂ c } :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (Integral X₂.scheme Y₂.scheme 0)
      (Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme 0)
      sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
      (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ targetGroup))

/-- Integral projection-pullback/intersection is additive in its first correspondence. -/
theorem integralTensorRight_add (X₁ X₂ Y₁ Y₂ : Category k)
    (c₁ c₂ : Integral X₁.scheme Y₁.scheme 0) (d : Integral X₂.scheme Y₂.scheme 0) :
    integralTensorRight X₁ X₂ Y₁ Y₂
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd 0 c₁ c₂) d =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd 0
        (integralTensorRight X₁ X₂ Y₁ Y₂ c₁ d)
        (integralTensorRight X₁ X₂ Y₁ Y₂ c₂ d) := sorry

/-- Integral projection-pullback/intersection respects integer scaling in its first input. -/
theorem integralTensorRight_zsmul (X₁ X₂ Y₁ Y₂ : Category k) (n : ℤ)
    (c : Integral X₁.scheme Y₁.scheme 0) (d : Integral X₂.scheme Y₂.scheme 0) :
    integralTensorRight X₁ X₂ Y₁ Y₂
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd 0 c n) d =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd 0
        (integralTensorRight X₁ X₂ Y₁ Y₂ c d) n := sorry

/-- The integral bilinear pairing `(c, d) ↦ pr₁₃⁎c · pr₂₄⁎d`, with all additive
structures supplied explicitly. -/
def integralTensor (X₁ X₂ Y₁ Y₂ : Category k) :=
  let firstGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) 0
  let secondGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) 0
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
      (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) 0
  @LinearMap.mk₂ ℤ inferInstance (Integral X₁.scheme Y₁.scheme 0)
    (Integral X₂.scheme Y₂.scheme 0)
    (Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme 0)
    firstGroup.toAddCommMonoid secondGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ firstGroup) (@AddCommGroup.toIntModule _ secondGroup)
    (@AddCommGroup.toIntModule _ targetGroup) (integralIntersection X₁ X₂ Y₁ Y₂)
    (integralTensorRight_add X₁ X₂ Y₁ Y₂)
    (integralTensorRight_zsmul X₁ X₂ Y₁ Y₂)
    (integralIntersection_add_right X₁ X₂ Y₁ Y₂)
    (fun n c d ↦ integralIntersection_zsmul_right X₁ X₂ Y₁ Y₂ c n d)

/-- The tensor product of rational correspondences obtained by scalar extension of the
integral projection-intersection pairing. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : Category k} (c : Rational X₁.scheme Y₁.scheme 0)
    (d : Rational X₂.scheme Y₂.scheme 0) :
    Rational (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme 0 :=
  let firstGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) 0
  let secondGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) 0
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
      (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) 0
  let f := integralTensor X₁ X₂ Y₁ Y₂
  let _ := firstGroup
  let _ := secondGroup
  let _ := targetGroup
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ
      (Integral X₁.scheme Y₁.scheme 0 →ₗ[ℤ]
        (ℚ ⊗[ℤ] Integral X₂.scheme Y₂.scheme 0) →ₗ[ℚ]
          (ℚ ⊗[ℤ] Integral (Category.product X₁ X₂).scheme
            (Category.product Y₁ Y₂).scheme 0))
      ((LinearMap.baseChangeHom ℤ ℚ (Integral X₂.scheme Y₂.scheme 0)
          (Integral (Category.product X₁ X₂).scheme
            (Category.product Y₁ Y₂).scheme 0)).comp f)) c d

/-- On pure rational tensors, `tensorHom` is the rationalized intersection of the two
projection pullbacks. -/
theorem tensorHom_tmul {X₁ Y₁ X₂ Y₂ : Category k} (a b : ℚ)
    (c : Integral X₁.scheme Y₁.scheme 0) (d : Integral X₂.scheme Y₂.scheme 0) :
    tensorHom
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X₁.scheme Y₁.scheme 0)
          inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) 0).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) 0)) a c)
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X₂.scheme Y₂.scheme 0)
          inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) 0).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) 0)) b d) =
      @TensorProduct.tmul ℤ inferInstance ℚ
        (Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme 0)
        inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
          (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
            (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) 0).toAddCommMonoid
        inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
          (fun _ ↦ 0) (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
            (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) 0))
        (a * b) (integralIntersection X₁ X₂ Y₁ Y₂ c d) := sorry


/-- The intersection of two projection pullbacks of integral correspondences of
arbitrary degrees. -/
def gradedIntegralIntersection (X₁ X₂ Y₁ Y₂ : Category k) {r s : ℤ}
    (c : Integral X₁.scheme Y₁.scheme r) (d : Integral X₂.scheme Y₂.scheme s) :
    Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme (r + s) :=
  Eq.mp
    (congrArg (fun f ↦ BivariantClass (fun _ ↦ 0) f (r + s))
      (projectionTargets_comp X₁ X₂ Y₁ Y₂))
    (BivariantClass.comp (fun _ ↦ 0) (projection13Target X₁ X₂ Y₁ Y₂)
      (projection24Target X₂ Y₁ Y₂)
      (BivariantClass.restrict (fun _ ↦ 0) (projection13 X₁ X₂ Y₁ Y₂)
        (projection13Target X₁ X₂ Y₁ Y₂) Limits.prod.fst
        (projection13_isPullback X₁ X₂ Y₁ Y₂) r c)
      (BivariantClass.restrict (fun _ ↦ 0) (projection24 X₂ Y₁ Y₂)
        (projection24Target X₂ Y₁ Y₂) Limits.prod.snd
        (projection24_isPullback X₂ Y₁ Y₂) s d))

/-- Graded projection-pullback/intersection is additive in its second correspondence. -/
theorem gradedIntegralIntersection_add_right (X₁ X₂ Y₁ Y₂ : Category k) {r s : ℤ}
    (c : Integral X₁.scheme Y₁.scheme r) (d₁ d₂ : Integral X₂.scheme Y₂.scheme s) :
    gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd s d₁ d₂) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd (r + s)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d₁)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d₂) := sorry

/-- Graded projection-pullback/intersection respects integer scaling in its second
input. -/
theorem gradedIntegralIntersection_zsmul_right (X₁ X₂ Y₁ Y₂ : Category k) {r s : ℤ}
    (c : Integral X₁.scheme Y₁.scheme r) (n : ℤ)
    (d : Integral X₂.scheme Y₂.scheme s) :
    gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd s d n) =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d) n := sorry

/-- Graded projection-pullback/intersection is additive in its first correspondence. -/
theorem gradedTensorRight_add (X₁ X₂ Y₁ Y₂ : Category k) {r s : ℤ}
    (c₁ c₂ : Integral X₁.scheme Y₁.scheme r) (d : Integral X₂.scheme Y₂.scheme s) :
    gradedIntegralIntersection X₁ X₂ Y₁ Y₂
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r c₁ c₂) d =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd (r + s)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c₁ d)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c₂ d) := sorry

/-- Graded projection-pullback/intersection respects integer scaling in its first
input. -/
theorem gradedTensorRight_zsmul (X₁ X₂ Y₁ Y₂ : Category k) {r s : ℤ} (n : ℤ)
    (c : Integral X₁.scheme Y₁.scheme r) (d : Integral X₂.scheme Y₂.scheme s) :
    gradedIntegralIntersection X₁ X₂ Y₁ Y₂
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd r c n) d =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d) n := sorry

/-- The graded integral bilinear pairing `(c, d) ↦ pr₁₃⁎c · pr₂₄⁎d`, with all additive
structures supplied explicitly. -/
def gradedTensor (X₁ X₂ Y₁ Y₂ : Category k) (r s : ℤ) :=
  let firstGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) r
  let secondGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
      (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) (r + s)
  @LinearMap.mk₂ ℤ inferInstance (Integral X₁.scheme Y₁.scheme r)
    (Integral X₂.scheme Y₂.scheme s)
    (Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme (r + s))
    firstGroup.toAddCommMonoid secondGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ firstGroup) (@AddCommGroup.toIntModule _ secondGroup)
    (@AddCommGroup.toIntModule _ targetGroup)
    (fun c d ↦ gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d)
    (fun c₁ c₂ d ↦ gradedTensorRight_add X₁ X₂ Y₁ Y₂ c₁ c₂ d)
    (fun n c d ↦ gradedTensorRight_zsmul X₁ X₂ Y₁ Y₂ n c d)
    (fun c d₁ d₂ ↦ gradedIntegralIntersection_add_right X₁ X₂ Y₁ Y₂ c d₁ d₂)
    (fun n c d ↦ gradedIntegralIntersection_zsmul_right X₁ X₂ Y₁ Y₂ c n d)

/-- The tensor product of rational correspondences of arbitrary degrees, obtained by
scalar extension of the graded integral projection-intersection pairing. -/
def tensor {X₁ Y₁ X₂ Y₂ : Category k} {r s : ℤ}
    (c : Rational X₁.scheme Y₁.scheme r) (d : Rational X₂.scheme Y₂.scheme s) :
    Rational (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme (r + s) :=
  let firstGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) r
  let secondGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
      (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) (r + s)
  let f := gradedTensor X₁ X₂ Y₁ Y₂ r s
  let _ := firstGroup
  let _ := secondGroup
  let _ := targetGroup
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ
      (Integral X₁.scheme Y₁.scheme r →ₗ[ℤ]
        (ℚ ⊗[ℤ] Integral X₂.scheme Y₂.scheme s) →ₗ[ℚ]
          (ℚ ⊗[ℤ] Integral (Category.product X₁ X₂).scheme
            (Category.product Y₁ Y₂).scheme (r + s)))
      ((LinearMap.baseChangeHom ℤ ℚ (Integral X₂.scheme Y₂.scheme s)
          (Integral (Category.product X₁ X₂).scheme
            (Category.product Y₁ Y₂).scheme (r + s))).comp f)) c d

/-- On pure rational tensors, graded `tensor` is the rationalized intersection of the two
projection pullbacks. -/
theorem tensor_tmul {X₁ Y₁ X₂ Y₂ : Category k} {r s : ℤ} (a b : ℚ)
    (c : Integral X₁.scheme Y₁.scheme r) (d : Integral X₂.scheme Y₂.scheme s) :
    tensor
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X₁.scheme Y₁.scheme r)
          inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) r).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X₁.scheme ⨯ Y₁.scheme ⟶ Y₁.scheme) r)) a c)
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X₂.scheme Y₂.scheme s)
          inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) s).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X₂.scheme ⨯ Y₂.scheme ⟶ Y₂.scheme) s)) b d) =
      @TensorProduct.tmul ℤ inferInstance ℚ
        (Integral (Category.product X₁ X₂).scheme (Category.product Y₁ Y₂).scheme (r + s))
        inferInstance (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
          (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
            (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) (r + s)).toAddCommMonoid
        inferInstance (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
          (fun _ ↦ 0) (Limits.prod.snd : (Category.product X₁ X₂).scheme ⨯
            (Category.product Y₁ Y₂).scheme ⟶ (Category.product Y₁ Y₂).scheme) (r + s)))
        (a * b) (gradedIntegralIntersection X₁ X₂ Y₁ Y₂ c d) := sorry

/-- In degree zero, the graded tensor agrees with the degree-zero tensor morphism. -/
theorem tensor_degreeZero {X₁ Y₁ X₂ Y₂ : Category k}
    (c : Rational X₁.scheme Y₁.scheme 0) (d : Rational X₂.scheme Y₂.scheme 0) :
    tensor c d = tensorHom c d := sorry

end AlgebraicGeometry.Correspondence
