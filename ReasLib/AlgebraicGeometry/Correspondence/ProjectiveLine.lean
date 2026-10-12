/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Transpose.Graph
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import Mathlib.Algebra.Ring.MinimalAxioms

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.ProjectiveLine

variable {k : Type u} [Field k]

/-- The self-product `ℙ¹_k ×ₖ ℙ¹_k`. -/
abbrev Product (k : Type u) [Field k] : SchemeOverField k :=
  ProjectiveSpace.schemeOver k 1 ⨯ ProjectiveSpace.schemeOver k 1

/-- The self-product of the projective line is locally of finite type over its base field. -/
instance productLocallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Product k).hom := sorry

/-- Degree-zero rational self-correspondences of `ℙ¹_k`. -/
abbrev End (k : Type u) [Field k] : Type (u + 1) :=
  Rational (ProjectiveSpace.schemeOver k 1) (ProjectiveSpace.schemeOver k 1) 0

/-- The self-product of the projective line is smooth over its base field. -/
instance productSmooth (k : Type u) [Field k] : Smooth (Product k).hom := sorry

/-- The self-product of the projective line is projective over its base field. -/
instance productProjective (k : Type u) [Field k] : Projective (Product k).hom := sorry

/-- The self-product of the projective line is equidimensional. -/
instance productEquidimensional (k : Type u) [Field k] :
    EquidimensionalSpace (Product k).left := sorry

/-- The projective line has topological Krull dimension one. -/
theorem lineDimension (k : Type u) [Field k] :
    topologicalKrullDim (ProjectiveSpace.schemeOver k 1).left =
      (1 : WithBot ℕ∞) := sorry

/-- The self-product of the projective line has topological Krull dimension two. -/
theorem productDimension (k : Type u) [Field k] :
    topologicalKrullDim (Product k).left = (2 : WithBot ℕ∞) := sorry

/-- Rational one-dimensional Chow homology of `ℙ¹_k ×ₖ ℙ¹_k`. -/
abbrev Homology (k : Type u) [Field k] : Type u :=
  RationalChowHomology (Product k) 1

/-- Rational codimension-one operational Chow cohomology of `ℙ¹_k ×ₖ ℙ¹_k`. -/
abbrev Cohomology (k : Type u) [Field k] : Type (u + 1) :=
  RationalChowCohomology (Product k) 1

/-- Realization identifies degree-zero self-correspondences with rational one-cycles
on `ℙ¹_k ×ₖ ℙ¹_k`. -/
noncomputable def toHomology (k : Type u) [Field k] : End k ≃ₗ[ℚ] Homology k :=
  realizationEquiv (ProjectiveSpace.schemeOver k 1)
    (ProjectiveSpace.schemeOver k 1) 1 (lineDimension k) 0

/-- The homological comparison is the established correspondence realization map. -/
theorem toHomology_apply (k : Type u) [Field k] (c : End k) :
    toHomology k c = realizationEquiv (ProjectiveSpace.schemeOver k 1)
      (ProjectiveSpace.schemeOver k 1) 1 (lineDimension k) 0 c := sorry

/-- The fundamental Chow class of `ℙ¹_k ×ₖ ℙ¹_k` in dimension two. -/
noncomputable def productFundamentalClass (k : Type u) [Field k] :
    RelativeChow (fun _ ↦ 0) (Product k) 2 :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @UniversallyCatenary.toIsLocallyNoetherian _
      (@instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
  let hProduct : IsLocallyNoetherian (Product k).left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (Product k).hom inferInstance hBase
  @chowClass (Product k).left hProduct
    ((Product k).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 2
    (@CycleGroup.fundamental (Product k).left hProduct
      ((Product k).hom.relativeDimensionFunction (fun _ ↦ 0)) 2)

/-- The product fundamental class is represented by its fundamental cycle. -/
theorem productFundamentalClass_def (k : Type u) [Field k] :
    productFundamentalClass k =
      let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
        @UniversallyCatenary.toIsLocallyNoetherian _
          (@instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _))
      let hProduct : IsLocallyNoetherian (Product k).left :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ (Product k).hom inferInstance hBase
      @chowClass (Product k).left hProduct
        ((Product k).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 2
        (@CycleGroup.fundamental (Product k).left hProduct
          ((Product k).hom.relativeDimensionFunction (fun _ ↦ 0)) 2) := sorry

/-- Capping with the product fundamental class as an additive map on integral classes. -/
noncomputable def integralPoincareDualityMap (k : Type u) [Field k] :=
  let sourceAddZero : AddZero (BivariantClass (fun _ ↦ 0) (𝟙 (Product k)) 1) :=
    { zero := BivariantClass.pointwiseZero (fun _ ↦ 0) (𝟙 (Product k)) 1
      add := BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 (Product k)) 1 }
  @AddMonoidHom.mk _ _ sourceAddZero inferInstance
    (@ZeroHom.mk _ _ sourceAddZero.toZero inferInstance
      (fun c ↦ c.cap (𝟙 (Product k)) (𝟙 (Product k)) (𝟙 (Product k))
        IsPullback.of_id_fst 2 (productFundamentalClass k)) sorry) sorry

/-- A chosen additive inverse to integral Poincare duality. -/
noncomputable def integralPoincareDualityInverse (k : Type u) [Field k] :=
  let targetAddZero : AddZero (BivariantClass (fun _ ↦ 0) (𝟙 (Product k)) 1) :=
    { zero := BivariantClass.pointwiseZero (fun _ ↦ 0) (𝟙 (Product k)) 1
      add := BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 (Product k)) 1 }
  @AddMonoidHom.mk _ _ inferInstance targetAddZero
    (@ZeroHom.mk _ _ inferInstance targetAddZero.toZero
      (Function.invFun (integralPoincareDualityMap k)) sorry) sorry

/-- Integral Poincare duality followed by its inverse recovers the operational class. -/
theorem integralPoincareDualityInverse_left (k : Type u) [Field k]
    (c : BivariantClass (fun _ ↦ 0) (𝟙 (Product k)) 1) :
    integralPoincareDualityInverse k (integralPoincareDualityMap k c) = c := sorry

/-- The inverse followed by integral Poincare duality recovers the Chow class. -/
theorem integralPoincareDualityInverse_right (k : Type u) [Field k]
    (c : RelativeChow (fun _ ↦ 0) (Product k) 1) :
    integralPoincareDualityMap k (integralPoincareDualityInverse k c) = c := sorry

/-- Poincare duality identifies rational codimension-one operational Chow classes
with rational one-dimensional Chow classes on `ℙ¹_k ×ₖ ℙ¹_k`. -/
noncomputable def poincareDuality (k : Type u) [Field k] :
    Cohomology k ≃ₗ[ℚ] Homology k :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup
    (fun _ ↦ 0) (𝟙 (Product k)) 1
  let integral :
      @AddEquiv (BivariantClass (fun _ ↦ 0) (𝟙 (Product k)) 1)
        (RelativeChow (fun _ ↦ 0) (Product k) 1) sourceGroup.toAdd inferInstance :=
    @AddEquiv.mk _ _ sourceGroup.toAdd inferInstance
      (@Equiv.mk _ _ (integralPoincareDualityMap k)
        (integralPoincareDualityInverse k)
        (integralPoincareDualityInverse_left k)
        (integralPoincareDualityInverse_right k))
      (integralPoincareDualityMap k).map_add
  let forward := (@AddEquiv.toIntLinearEquiv _ _ sourceGroup inferInstance
    (@AddCommGroup.toIntModule _ sourceGroup) inferInstance integral).toLinearMap.baseChange ℚ
  let inverse := (@AddEquiv.toIntLinearEquiv _ _ inferInstance sourceGroup
    inferInstance (@AddCommGroup.toIntModule _ sourceGroup) integral.symm).toLinearMap.baseChange ℚ
  { toFun := forward
    map_add' := forward.map_add
    map_smul' := forward.map_smul
    invFun := inverse
    left_inv := sorry
    right_inv := sorry }

/-- Poincare duality is scalar extension of capping with the product fundamental class. -/
theorem poincareDuality_apply (k : Type u) [Field k] (c : Cohomology k) :
    poincareDuality k c =
      let sourceGroup := BivariantClass.pointwiseAddCommGroup
        (fun _ ↦ 0) (𝟙 (Product k)) 1
      (@AddMonoidHom.toIntLinearMap _ _ sourceGroup inferInstance
        (integralPoincareDualityMap k)).baseChange ℚ c := sorry

/-- The codimension-one realization of a degree-zero self-correspondence. -/
noncomputable def toCohomology (k : Type u) [Field k] : End k ≃ₗ[ℚ] Cohomology k :=
  (toHomology k).trans (poincareDuality k).symm

/-- The cohomological realization is homological realization followed by inverse
Poincare duality. -/
theorem toCohomology_apply (k : Type u) [Field k] (c : End k) :
    toCohomology k c = (poincareDuality k).symm (toHomology k c) := sorry

/-- The constant endomorphism of `ℙ¹_k` with value the rational point `x`. -/
def constant
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ProjectiveSpace.schemeOver k 1 ⟶ ProjectiveSpace.schemeOver k 1 :=
  terminal.from (ProjectiveSpace.schemeOver k 1) ≫ x

/-- The constant endomorphism factors through the chosen rational point. -/
theorem constant_def
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    constant x = terminal.from (ProjectiveSpace.schemeOver k 1) ≫ x := sorry

/-- The rational correspondence represented by `[x × ℙ¹_k]`. -/
noncomputable def pointTimes
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) : End k :=
  Correspondence.rationalGraph (constant x)

/-- Realizing `pointTimes x` gives the rational graph class `[x × ℙ¹_k]`. -/
theorem toHomology_pointTimes
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    toHomology k (pointTimes x) = graphClass 1 (lineDimension k) (constant x) := sorry

/-- The rational correspondence represented by `[ℙ¹_k × x]`. -/
noncomputable def timesPoint
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) : End k :=
  transposedGraph (ProjectiveSpace.schemeOver k 1) (ProjectiveSpace.schemeOver k 1)
    1 1 (lineDimension k) (lineDimension k) (constant x)

/-- Realizing `timesPoint x` gives the rational transposed-graph class `[ℙ¹_k × x]`. -/
theorem toHomology_timesPoint
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    toHomology k (timesPoint x) =
      transposedGraphClass 1 1 (lineDimension k) (constant x) := sorry

/-- The diagonal correspondence of `ℙ¹_k`, defined as the rational graph of the identity. -/
noncomputable def diagonal (k : Type u) [Field k] : End k :=
  Correspondence.rationalGraph (𝟙 (ProjectiveSpace.schemeOver k 1))

/-- Realizing the diagonal correspondence gives the rational identity-graph class. -/
theorem toHomology_diagonal (k : Type u) [Field k] :
    toHomology k (diagonal k) = graphClass 1 (lineDimension k) (𝟙 _) := sorry

/-- Multiplication of degree-zero self-correspondences is correspondence composition. -/
noncomputable instance instMulEnd (k : Type u) [Field k] : Mul (End k) :=
  ⟨fun c d ↦ Correspondence.composition (ProjectiveSpace.schemeOver k 1)
    (ProjectiveSpace.schemeOver k 1) (ProjectiveSpace.schemeOver k 1) 0 0 c d⟩

/-- The multiplicative unit is the geometric diagonal correspondence. -/
noncomputable instance instOneEnd (k : Type u) [Field k] : One (End k) :=
  ⟨diagonal k⟩

/-- Composition of degree-zero self-correspondences is associative. -/
theorem composition_assoc (a b c : End k) : (a * b) * c = a * (b * c) := sorry

/-- The diagonal is a left unit for correspondence composition. -/
theorem diagonal_mul (a : End k) : diagonal k * a = a := sorry

/-- The diagonal is a right unit for correspondence composition. -/
theorem mul_diagonal (a : End k) : a * diagonal k = a := sorry

/-- Correspondence composition distributes over addition on the right. -/
theorem composition_add (a b c : End k) : a * (b + c) = a * b + a * c := sorry

/-- Correspondence composition distributes over addition on the left. -/
theorem add_composition (a b c : End k) : (a + b) * c = a * c + b * c := sorry

/-- The canonical ring structure on degree-zero projective-line self-correspondences. -/
noncomputable instance instRingEnd (k : Type u) [Field k] : Ring (End k) :=
  Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel composition_assoc
    diagonal_mul mul_diagonal composition_add add_composition

/-- Ring multiplication is the established pull-intersect-push composition. -/
theorem mul_eq_composition (a b : End k) :
    a * b = Correspondence.composition (ProjectiveSpace.schemeOver k 1)
      (ProjectiveSpace.schemeOver k 1) (ProjectiveSpace.schemeOver k 1) 0 0 a b := sorry

/-- The canonical `ℚ`-algebra structure acts by scalar multiples of the diagonal. -/
noncomputable instance instAlgebraEnd (k : Type u) [Field k] : Algebra ℚ (End k) where
  smul := fun q c ↦ q • c
  algebraMap :=
    { toFun := fun q ↦ q • diagonal k
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }
  commutes' := sorry
  smul_def' := sorry

/-- The algebra map sends `q` to `q • diagonal k`. -/
theorem algebraMap_apply (q : ℚ) :
    algebraMap ℚ (End k) q = q • diagonal k := sorry

/-- The multiplicative unit is the diagonal correspondence. -/
theorem one_eq_diagonal : (1 : End k) = diagonal k := sorry

/-- The diagonal splits as the sum of the two point correspondences. -/
theorem diagonal_eq_add
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    diagonal k = pointTimes x + timesPoint x := sorry

/-- The correspondence `[x × ℙ¹_k]` is idempotent. -/
theorem pointTimes_mul_pointTimes
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    pointTimes x * pointTimes x = pointTimes x := sorry

/-- The ordered product `[x × ℙ¹_k] * [ℙ¹_k × x]` is zero. -/
theorem pointTimes_mul_timesPoint
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    pointTimes x * timesPoint x = 0 := sorry

/-- The ordered product `[ℙ¹_k × x] * [x × ℙ¹_k]` is zero. -/
theorem timesPoint_mul_pointTimes
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    timesPoint x * pointTimes x = 0 := sorry

/-- The correspondence `[ℙ¹_k × x]` is idempotent. -/
theorem timesPoint_mul_timesPoint
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    timesPoint x * timesPoint x = timesPoint x := sorry

/-- The algebra homomorphism `(a, b) ↦ a • [x × ℙ¹_k] + b • [ℙ¹_k × x]`. -/
noncomputable def fromProd
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ℚ × ℚ →ₐ[ℚ] End k where
  toFun := fun a ↦ a.1 • pointTimes x + a.2 • timesPoint x
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The projective-line algebra map is the prescribed linear combination of point cycles. -/
theorem fromProd_apply
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) (a : ℚ × ℚ) :
    fromProd x a = a.1 • pointTimes x + a.2 • timesPoint x := sorry

/-- The two point correspondences coordinatize all degree-zero projective-line
self-correspondences. -/
theorem fromProd_bijective
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    Function.Bijective (fromProd x) := sorry

end AlgebraicGeometry.Correspondence.ProjectiveLine
