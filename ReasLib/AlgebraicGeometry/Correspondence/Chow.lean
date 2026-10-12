/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.Rationalization
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import ReasLib.LinearAlgebra.BilinearMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The field point is locally of finite type over itself. -/
instance point_locallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom := sorry

/-- The first product projection is proper when the second factor is proper over the field. -/
instance productFst_isProper (X Y : SchemeOverField k) [IsProper Y.hom] :
    IsProper (Limits.prod.fst : X ⨯ Y ⟶ X).left := sorry

/-- The second product projection is proper when the first factor is proper over the field. -/
instance productSnd_isProper (X Y : SchemeOverField k) [IsProper X.hom] :
    IsProper (Limits.prod.snd : X ⨯ Y ⟶ Y).left := sorry

/-- Transport a bivariant class along equality of its underlying morphism. -/
def castHom {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {f g : X ⟶ Y} (h : f = g) (p : ℤ) :
    BivariantClass (fun _ ↦ 0) f p → BivariantClass (fun _ ↦ 0) g p :=
  fun c ↦ h ▸ c

/-- `castHom` is the direct transport along the supplied morphism equality. -/
theorem castHom_apply {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {f g : X ⟶ Y} (h : f = g) (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) f p) : castHom h p c = h ▸ c := sorry

/-- The product projections over a field form a pullback square against maps to its point. -/
theorem pointProductIsPullback (X : SchemeOverField k) {Y : SchemeOverField k}
    (g : Y ⟶ SchemeOverField.point k) :
    IsPullback (Limits.prod.fst : X ⨯ Y ⟶ X).left
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left (terminal.from X).left g.left := sorry

/-- The canonical pullback comparison with `X ⨯ Y` respects the structure maps. -/
theorem pointProductIso_hom_base
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (square.isoIsPullback X.left Y.left (pointProductIsPullback X g)).hom ≫
        (X ⨯ Y).hom = X'.hom := sorry

/-- The canonical isomorphism from a cartesian representative over the point to a product. -/
noncomputable def pointProductIso
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    X' ≅ X ⨯ Y :=
  Over.isoMk (square.isoIsPullback X.left Y.left (pointProductIsPullback X g))
    (pointProductIso_hom_base X i f' g square)

/-- The point-product comparison followed by the first projection is the given map. -/
theorem pointProductIso_hom_fst
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (pointProductIso X i f' g square).hom ≫ Limits.prod.fst = i := sorry

/-- The degree-zero fundamental Chow class of the spectrum of the ground field. -/
noncomputable def pointFundamentalClass (k : Type u) [Field k] :
    RelativeChow (fun _ ↦ 0) (SchemeOverField.point k) 0 :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @UniversallyCatenary.toIsLocallyNoetherian _
      (@instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
  let hPoint : IsLocallyNoetherian (SchemeOverField.point k).left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (SchemeOverField.point k).hom
      inferInstance hBase
  @chowClass (SchemeOverField.point k).left hPoint
    ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 0
    (@CycleGroup.fundamental (SchemeOverField.point k).left hPoint
      ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0)) 0)

/-- The point fundamental class is represented by its degree-zero fundamental cycle. -/
theorem pointFundamentalClass_def (k : Type u) [Field k] :
    pointFundamentalClass k =
      @chowClass (SchemeOverField.point k).left
        (LocallyOfFiniteType.isLocallyNoetherian (SchemeOverField.point k).hom)
        ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0))
        inferInstance 0
        (@CycleGroup.fundamental (SchemeOverField.point k).left
          (LocallyOfFiniteType.isLocallyNoetherian (SchemeOverField.point k).hom)
          ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0)) 0) := sorry

/-- The cap family obtained by exterior product with a Chow class. -/
noncomputable def ofChowCap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CapFamily (fun _ ↦ 0) (terminal.from X) p :=
  fun {X' Y'} _ _ i f' g _ square n ↦
    (ChowGroup.map (fun _ ↦ 0) (X ⨯ Y') X'
      (pointProductIso X i f' g square).inv (n - p)).comp
      ((BivariantClass.castRelativeDegree (fun _ ↦ 0) (neg_add_eq_sub p n)).comp
        (ChowGroup.exteriorProductPairing X Y' (-p) n alpha))

/-- Evaluation of the exterior-product cap family uses the point-product comparison. -/
theorem ofChowCap_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p))
    {X' Y' : SchemeOverField k} [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ SchemeOverField.point k)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (terminal.from X).left g.left)
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y' n) :
    ofChowCap X p alpha i f' g square n beta =
      ChowGroup.map (fun _ ↦ 0) (X ⨯ Y') X'
        (pointProductIso X i f' g square).inv (n - p)
        (BivariantClass.castRelativeDegree (fun _ ↦ 0) (neg_add_eq_sub p n)
          (ChowGroup.exteriorProductPairing X Y' (-p) n alpha beta)) := sorry

/-- Exterior-product cap families commute with proper pushforward. -/
theorem ofChowCap_mapProper (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithProperPushforward (fun _ ↦ 0)
      (ofChowCap X p alpha) := sorry

/-- Exterior-product cap families commute with flat pullback. -/
theorem ofChowCap_pullbackFlat (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithFlatPullback (fun _ ↦ 0)
      (ofChowCap X p alpha) := sorry

/-- Exterior-product cap families commute with effective-Cartier Gysin pullback. -/
theorem ofChowCap_gysinCartier (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithCartierGysin (fun _ ↦ 0)
      (ofChowCap X p alpha) := sorry

/-- The bivariant class whose action is exterior product with a Chow class. -/
noncomputable def ofChowClass (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass (fun _ ↦ 0) (terminal.from X) p where
  cap := ofChowCap X p alpha
  map_proper := ofChowCap_mapProper X p alpha
  pullback_flat := ofChowCap_pullbackFlat X p alpha
  gysin_cartier := ofChowCap_gysinCartier X p alpha

/-- The cap field of `ofChowClass` is the exterior-product cap family. -/
theorem ofChowClass_cap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p))
    {X' Y' : SchemeOverField k} [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ SchemeOverField.point k)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (terminal.from X).left g.left)
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y' n) :
    (ofChowClass X p alpha).cap i f' g square n beta =
      ofChowCap X p alpha i f' g square n beta := sorry

section PointComparison

/-- Exterior product defines an additive map from Chow classes to bivariant classes. -/
noncomputable def ofChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  let targetAddZero : AddZero (BivariantClass (fun _ ↦ 0) (terminal.from X) p) :=
    { zero := BivariantClass.pointwiseZero (fun _ ↦ 0) (terminal.from X) p
      add := BivariantClass.pointwiseAdd (fun _ ↦ 0) (terminal.from X) p }
  @AddMonoidHom.mk (RelativeChow (fun _ ↦ 0) X (-p))
    (BivariantClass (fun _ ↦ 0) (terminal.from X) p) inferInstance targetAddZero
    (@ZeroHom.mk _ _ inferInstance targetAddZero.toZero (ofChowClass X p) sorry) sorry

/-- The additive map `ofChow` sends a class to its exterior-product bivariant class. -/
theorem ofChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChow X p alpha = ofChowClass X p alpha := sorry

/-- Evaluation of a bivariant class on the fundamental class of the field point. -/
noncomputable def toChowValue (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    RelativeChow (fun _ ↦ 0) X (-p) :=
  BivariantClass.castRelativeDegree (fun _ ↦ 0) (zero_sub p)
    (c.cap (𝟙 X) (terminal.from X) (𝟙 (SchemeOverField.point k))
      IsPullback.of_id_fst 0 (pointFundamentalClass k))

/-- Evaluation on the field point is the formal cap product with its fundamental class. -/
theorem toChowValue_def (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p c =
      BivariantClass.castRelativeDegree (fun _ ↦ 0) (zero_sub p)
        (c.cap (𝟙 X) (terminal.from X) (𝟙 (SchemeOverField.point k))
          IsPullback.of_id_fst 0 (pointFundamentalClass k)) := sorry

/-- Evaluation on the field point as an additive map. -/
noncomputable def toChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  let sourceAddZero : AddZero (BivariantClass (fun _ ↦ 0) (terminal.from X) p) :=
    { zero := BivariantClass.pointwiseZero (fun _ ↦ 0) (terminal.from X) p
      add := BivariantClass.pointwiseAdd (fun _ ↦ 0) (terminal.from X) p }
  @AddMonoidHom.mk (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
    (RelativeChow (fun _ ↦ 0) X (-p)) sourceAddZero inferInstance
    (@ZeroHom.mk _ _ sourceAddZero.toZero inferInstance (toChowValue X p) sorry) sorry

/-- The additive map `toChow` evaluates on the field-point fundamental class. -/
theorem toChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChow X p c = toChowValue X p c := sorry

/-- The canonical additive identification of Chow classes with bivariant classes over
the field point. -/
noncomputable def pointChowEquiv (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  let sourceAdd : Add (BivariantClass (fun _ ↦ 0) (terminal.from X) p) :=
    { add := BivariantClass.pointwiseAdd (fun _ ↦ 0) (terminal.from X) p }
  @AddEquiv.mk (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
    (RelativeChow (fun _ ↦ 0) X (-p)) sourceAdd inferInstance
    (@Equiv.mk _ _ (toChow X p) (ofChow X p) sorry sorry) sorry

/-- The forward map of `pointChowEquiv` is evaluation on the field point. -/
theorem pointChowEquiv_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    pointChowEquiv X p c = toChow X p c := sorry

end PointComparison

/-- Integral Chow correspondences of degree `r` from `X` to `Y`, represented as
bivariant Chow classes of the second projection `X ⨯ Y ⟶ Y`. -/
abbrev Integral (X Y : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (r : ℤ) : Type (u + 1) :=
  BivariantClass (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r

/-- Rational Chow correspondences are obtained from integral correspondences by
extension of scalars from `ℤ` to `ℚ`. -/
abbrev Rational (X Y : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (r : ℤ) : Type (u + 1) :=
  BivariantClass.RationalBivariantClass (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r

/-- Rational Chow homology in degree `n`. -/
abbrev RationalChowHomology (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (n : ℤ) : Type u :=
  ℚ ⊗[ℤ] RelativeChow (fun _ ↦ 0) X n

/-- Rational operational Chow cohomology in degree `r`. -/
abbrev RationalChowCohomology (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (r : ℤ) : Type (u + 1) :=
  BivariantClass.RationalBivariantClass (fun _ ↦ 0) (𝟙 X) r

/-- The cartesian space on which two composable correspondences are intersected. -/
abbrev CompositionSpace (X Y Z : SchemeOverField k) : SchemeOverField k :=
  pullback (Limits.prod.snd : X ⨯ Y ⟶ Y) (Limits.prod.fst : Y ⨯ Z ⟶ Y)

/-- The correspondence-composition space is locally of finite type over the field. -/
instance compositionSpace_locallyOfFiniteType
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (CompositionSpace X Y Z).hom := sorry

/-- The underlying square defining the correspondence-composition space is cartesian. -/
theorem composition_isPullback (X Y Z : SchemeOverField k) :
    IsPullback
      (pullback.fst (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).left
      (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).left
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.fst : Y ⨯ Z ⟶ Y).left := sorry

/-- The first projection from a product is locally of finite type when its
second factor is locally of finite type over the field. -/
instance productFst_locallyOfFiniteType (Y Z : SchemeOverField k)
    [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (Limits.prod.fst : Y ⨯ Z ⟶ Y).left := sorry

/-- Projection from the correspondence-composition space to `X ⨯ Z`. -/
def compositionProjection (X Y Z : SchemeOverField k) :
    CompositionSpace X Y Z ⟶ X ⨯ Z :=
  Limits.prod.lift
    (pullback.fst (Limits.prod.snd : X ⨯ Y ⟶ Y) (Limits.prod.fst : Y ⨯ Z ⟶ Y) ≫
      (Limits.prod.fst : X ⨯ Y ⟶ X))
    (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y) (Limits.prod.fst : Y ⨯ Z ⟶ Y) ≫
      (Limits.prod.snd : Y ⨯ Z ⟶ Z))

/-- The projection used in correspondence composition is proper when the middle
scheme is projective over the field. -/
instance compositionProjection_isProper (X Y Z : SchemeOverField k)
    [AlgebraicGeometry.Projective Y.hom] :
    IsProper (compositionProjection X Y Z).left := sorry

/-- The projection to `Z` through `X ⨯ Z` agrees with the projection through
`Y ⨯ Z`. -/
theorem compositionProjection_snd (X Y Z : SchemeOverField k) :
    compositionProjection X Y Z ≫ (Limits.prod.snd : X ⨯ Z ⟶ Z) =
      pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y) ≫ (Limits.prod.snd : Y ⨯ Z ⟶ Z) := sorry

/-- The integral pull–intersect–push formula for composing correspondences. -/
def integralCompositionValue
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c : Integral X Y r) (d : Integral Y Z s) : Integral X Z (r + s) :=
  BivariantClass.properPushforward (fun _ ↦ 0) (compositionProjection X Y Z)
    (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
    ((compositionProjection_snd X Y Z).symm ▸
      BivariantClass.comp (fun _ ↦ 0)
        (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
          (Limits.prod.fst : Y ⨯ Z ⟶ Y))
        (Limits.prod.snd : Y ⨯ Z ⟶ Z)
        (BivariantClass.restrict (fun _ ↦ 0)
          (pullback.fst (Limits.prod.snd : X ⨯ Y ⟶ Y)
            (Limits.prod.fst : Y ⨯ Z ⟶ Y))
          (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
            (Limits.prod.fst : Y ⨯ Z ⟶ Y))
          (Limits.prod.fst : Y ⨯ Z ⟶ Y)
          (composition_isPullback X Y Z) r c)
        d)

/-- Integral correspondence composition is additive in its second variable. -/
theorem integralCompositionValue_add_right
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c : Integral X Y r) (d₁ d₂ : Integral Y Z s) :
    integralCompositionValue X Y Z c
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd s d₁ d₂) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionValue X Y Z c d₁)
        (integralCompositionValue X Y Z c d₂) := sorry

/-- Integral correspondence composition respects integer scaling in its second variable. -/
theorem integralCompositionValue_zsmul_right
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c : Integral X Y r) (n : ℤ) (d : Integral Y Z s) :
    integralCompositionValue X Y Z c
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd s d n) =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionValue X Y Z c d) n := sorry

section IntegralComposition

/-- Composition by a fixed integral correspondence as an integer-linear map. -/
def integralCompositionRight
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c : Integral X Y r) :=
  let sourceGroup :=
    BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
      (Limits.prod.snd : Y ⨯ Z ⟶ Z) s
  let targetGroup :=
    BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
  ({ toFun := integralCompositionValue X Y Z c
     map_add' := integralCompositionValue_add_right X Y Z c
     map_smul' := integralCompositionValue_zsmul_right X Y Z c } :
    @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (Integral Y Z s) (Integral X Z (r + s))
      sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
      (@AddCommGroup.toIntModule (Integral Y Z s) sourceGroup)
      (@AddCommGroup.toIntModule (Integral X Z (r + s)) targetGroup))

/-- Integral correspondence composition is additive in its first variable. -/
theorem integralCompositionRight_add
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c₁ c₂ : Integral X Y r) (d : Integral Y Z s) :
    integralCompositionRight X Y Z
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r c₁ c₂) d =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionRight X Y Z c₁ d)
        (integralCompositionRight X Y Z c₂ d) := sorry

/-- Integral correspondence composition respects integer scaling in its first variable. -/
theorem integralCompositionRight_zsmul
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (n : ℤ) (c : Integral X Y r) (d : Integral Y Z s) :
    integralCompositionRight X Y Z
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd r c n) d =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionRight X Y Z c d) n := sorry

/-- Integral pull–intersect–push composition as a bilinear map. -/
def integralComposition
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    (r s : ℤ) :=
  let sourceGroup :=
    BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let middleGroup :=
    BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
      (Limits.prod.snd : Y ⨯ Z ⟶ Z) s
  let targetGroup :=
    BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
  @LinearMap.mk₂ ℤ inferInstance (Integral X Y r) (Integral Y Z s)
    (Integral X Z (r + s)) sourceGroup.toAddCommMonoid middleGroup.toAddCommMonoid
    targetGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ sourceGroup)
    (@AddCommGroup.toIntModule _ middleGroup) (@AddCommGroup.toIntModule _ targetGroup)
    (integralCompositionValue X Y Z)
    (fun c₁ c₂ d ↦ integralCompositionRight_add X Y Z c₁ c₂ d)
    (fun n c d ↦ integralCompositionRight_zsmul X Y Z n c d)
    (integralCompositionValue_add_right X Y Z)
    (fun n c d ↦ integralCompositionValue_zsmul_right X Y Z c n d)

/-- Composition of rational Chow correspondences, obtained by extending the integral
pull–intersect–push pairing from `ℤ` to `ℚ`. -/
def composition
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    (r s : ℤ) : Rational X Y r →ₗ[ℚ] Rational Y Z s →ₗ[ℚ] Rational X Z (r + s) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let middleGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : Y ⨯ Z ⟶ Z) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
  @LinearMap.baseChange₂ ℤ ℚ (Integral X Y r) (Integral Y Z s)
    (Integral X Z (r + s)) inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ sourceGroup)
    middleGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ middleGroup)
    targetGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ targetGroup)
    (integralComposition X Y Z r s)

/-- On pure rational tensors, correspondence composition is the integral
pull–intersect–push composition with multiplied coefficients. -/
theorem composition_tmul
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (a b : ℚ) (c : Integral X Y r) (d : Integral Y Z s) :
    composition X Y Z r s
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X Y r) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X ⨯ Y ⟶ Y) r).toAddCommMonoid inferInstance
          (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r)) a c)
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral Y Z s) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : Y ⨯ Z ⟶ Z) s).toAddCommMonoid inferInstance
          (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : Y ⨯ Z ⟶ Z) s)) b d) =
      @TensorProduct.tmul ℤ inferInstance ℚ (Integral X Z (r + s)) inferInstance
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
          (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)).toAddCommMonoid inferInstance
        (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
          (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)))
        (a * b) (integralCompositionValue X Y Z c d) := sorry

end IntegralComposition

section RationalConstructions

/-- Transport a rational correspondence along an equality of grading indices. -/
def castDegree {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {r s : ℤ} (h : r = s) :
    Rational X Y r →ₗ[ℚ] Rational X Y s :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) s
  @LinearMap.baseChange ℤ ℚ (Integral X Y r) (Integral X Y s) inferInstance
    inferInstance inferInstance sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ targetGroup)
    (@AddMonoidHom.toIntLinearMap _ _ sourceGroup targetGroup
      (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h))

/-- The rational grading transport acts by scalar extension of the integral transport. -/
theorem castDegree_apply {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {r s : ℤ} (h : r = s) (c : Rational X Y r) :
    castDegree h c =
      @LinearMap.baseChange ℤ ℚ (Integral X Y r) (Integral X Y s) inferInstance
        inferInstance inferInstance
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
          (Limits.prod.snd : X ⨯ Y ⟶ Y) r).toAddCommMonoid
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
          (Limits.prod.snd : X ⨯ Y ⟶ Y) s).toAddCommMonoid
        (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
          (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r))
        (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
          (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) s))
        (@AddMonoidHom.toIntLinearMap _ _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X ⨯ Y ⟶ Y) r)
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X ⨯ Y ⟶ Y) s)
          (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h)) c := sorry

/-- Transport rational Chow homology along an equality of homological degrees. -/
def castHomologyDegree {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {m n : ℤ} (h : m = n) :
    RationalChowHomology X m →ₗ[ℚ] RationalChowHomology X n :=
  (BivariantClass.castRelativeDegree (fun _ ↦ 0) h).toIntLinearMap.baseChange ℚ

/-- Homological grading transport is scalar extension of integral grading transport. -/
theorem castHomologyDegree_apply {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {m n : ℤ} (h : m = n) (alpha : RationalChowHomology X m) :
    castHomologyDegree h alpha =
      (BivariantClass.castRelativeDegree (fun _ ↦ 0) h).toIntLinearMap.baseChange ℚ alpha := sorry

/-- Transport rational operational Chow cohomology along an equality of degrees. -/
def castCohomologyDegree {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {r s : ℤ} (h : r = s) :
    RationalChowCohomology X r →ₗ[ℚ] RationalChowCohomology X s :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  @LinearMap.baseChange ℤ ℚ (BivariantClass (fun _ ↦ 0) (𝟙 X) r)
    (BivariantClass (fun _ ↦ 0) (𝟙 X) s) inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ targetGroup)
    (@AddMonoidHom.toIntLinearMap _ _ sourceGroup targetGroup
      (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h))

/-- Cohomological grading transport is scalar extension of integral grading transport. -/
theorem castCohomologyDegree_apply {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {r s : ℤ} (h : r = s) (alpha : RationalChowCohomology X r) :
    castCohomologyDegree h alpha =
      @LinearMap.baseChange ℤ ℚ (BivariantClass (fun _ ↦ 0) (𝟙 X) r)
        (BivariantClass (fun _ ↦ 0) (𝟙 X) s) inferInstance inferInstance inferInstance
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r).toAddCommMonoid
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
        (@AddCommGroup.toIntModule _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r))
        (@AddCommGroup.toIntModule _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s))
        (@AddMonoidHom.toIntLinearMap _ _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r)
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s)
          (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h)) alpha := sorry

/-- The product projection followed by the structure map is the projection to the point. -/
theorem productFst_comp_toPoint (X : SchemeOverField k) :
    (Limits.prod.fst : X ⨯ SchemeOverField.point k ⟶ X) ≫ terminal.from X =
      (Limits.prod.snd : X ⨯ SchemeOverField.point k ⟶ SchemeOverField.point k) := sorry

/-- Pulling the identity of `X` back along the second projection from
`Spec k × X` gives the cartesian square presenting that projection. -/
theorem pointProductSndIsPullback (X : SchemeOverField k) :
    IsPullback
      (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X).left
      (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X).left
      (𝟙 X : X ⟶ X).left
      (𝟙 X : X ⟶ X).left := sorry

/-- Pulling the identity of `X` back along the first projection from `X × Y`
gives the cartesian square presenting that projection. -/
theorem productFstIdentityIsPullback (X Y : SchemeOverField k) :
    IsPullback
      (Limits.prod.fst : X ⨯ Y ⟶ X).left
      (𝟙 (X ⨯ Y) : X ⨯ Y ⟶ X ⨯ Y).left
      (𝟙 X : X ⟶ X).left
      (Limits.prod.fst : X ⨯ Y ⟶ X).left := sorry

/-- The grading identity for the action of a degree-`r` correspondence on
homological degree `-s`. -/
theorem pullbackDegree (r s : ℤ) : -s - r = -(r + s) := sorry

/-- Pullback of rational Chow homology by a rational correspondence, defined by
capping on `X × Y` and proper pushforward along the first projection. -/
def pullback (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ) :
    Rational X Y r →ₗ[ℚ]
      RationalChowHomology Y (-s) →ₗ[ℚ] RationalChowHomology X (-(r + s)) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let integralValue := fun (c : Integral X Y r)
      (alpha : RelativeChow (fun _ ↦ 0) Y (-s)) ↦
    ChowGroup.map (fun _ ↦ 0) (X ⨯ Y) X Limits.prod.fst (-(r + s))
      (BivariantClass.castRelativeDegree (fun _ ↦ 0) (pullbackDegree r s)
        (c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y) IsPullback.of_id_fst (-s) alpha))
  let integralPullback := @LinearMap.mk₂ ℤ inferInstance (Integral X Y r)
    (RelativeChow (fun _ ↦ 0) Y (-s)) (RelativeChow (fun _ ↦ 0) X (-(r + s)))
    sourceGroup.toAddCommMonoid inferInstance inferInstance
    (@AddCommGroup.toIntModule _ sourceGroup) inferInstance inferInstance integralValue
    sorry sorry sorry sorry
  @LinearMap.baseChange₂ ℤ ℚ _ _ _ inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ sourceGroup)
    inferInstance inferInstance inferInstance inferInstance integralPullback

/-- On pure tensors, correspondence pullback is the rationalization of cap followed
by pushforward along the first projection. -/
theorem pullback_tmul (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ) (a b : ℚ)
    (c : Integral X Y r) (alpha : RelativeChow (fun _ ↦ 0) Y (-s)) :
    pullback X Y r s
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X Y r) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X ⨯ Y ⟶ Y) r).toAddCommMonoid inferInstance
          (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r)) a c)
        (b ⊗ₜ[ℤ] alpha) =
      (a * b) ⊗ₜ[ℤ]
        ChowGroup.map (fun _ ↦ 0) (X ⨯ Y) X Limits.prod.fst (-(r + s))
          (BivariantClass.castRelativeDegree (fun _ ↦ 0) (pullbackDegree r s)
            (c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y)
              IsPullback.of_id_fst (-s) alpha)) := sorry

/-- Pushforward of rational operational Chow cohomology by a rational correspondence,
defined by pullback to `X × Y`, bivariant composition, and proper pushforward. -/
def pushforward (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ) :
    Rational X Y r →ₗ[ℚ]
      RationalChowCohomology X s →ₗ[ℚ] RationalChowCohomology Y (s + r) :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  let middleGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) (s + r)
  let integralValue := fun (c : Integral X Y r)
      (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) ↦
    let pulled := BivariantClass.restrict (fun _ ↦ 0)
      (Limits.prod.fst : X ⨯ Y ⟶ X) (𝟙 (X ⨯ Y))
      (Limits.prod.fst : X ⨯ Y ⟶ X) (productFstIdentityIsPullback X Y) s alpha
    let productClass := (Category.id_comp (Limits.prod.snd : X ⨯ Y ⟶ Y)) ▸
      BivariantClass.comp (fun _ ↦ 0) (𝟙 (X ⨯ Y))
        (Limits.prod.snd : X ⨯ Y ⟶ Y) pulled c
    BivariantClass.properPushforwardToTarget (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Y ⟶ Y) (s + r) productClass
  let integralPushforward := @LinearMap.mk₂ ℤ inferInstance (Integral X Y r)
    (BivariantClass (fun _ ↦ 0) (𝟙 X) s)
    (BivariantClass (fun _ ↦ 0) (𝟙 Y) (s + r)) sourceGroup.toAddCommMonoid
    middleGroup.toAddCommMonoid targetGroup.toAddCommMonoid
    (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ middleGroup)
    (@AddCommGroup.toIntModule _ targetGroup) integralValue sorry sorry sorry sorry
  @LinearMap.baseChange₂ ℤ ℚ _ _ _ inferInstance inferInstance inferInstance
    sourceGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ sourceGroup)
    middleGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ middleGroup)
    targetGroup.toAddCommMonoid (@AddCommGroup.toIntModule _ targetGroup) integralPushforward

/-- On pure tensors, correspondence pushforward is the rationalization of pullback
to the product, bivariant composition, and proper pushforward. -/
theorem pushforward_tmul (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ) (a b : ℚ)
    (c : Integral X Y r) (alpha : BivariantClass (fun _ ↦ 0) (𝟙 X) s) :
    pushforward X Y r s
        (@TensorProduct.tmul ℤ inferInstance ℚ (Integral X Y r) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
            (Limits.prod.snd : X ⨯ Y ⟶ Y) r).toAddCommMonoid inferInstance
          (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup
            (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r)) a c)
        (@TensorProduct.tmul ℤ inferInstance ℚ
          (BivariantClass (fun _ ↦ 0) (𝟙 X) s) inferInstance
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s).toAddCommMonoid
          inferInstance (@AddCommGroup.toIntModule _
            (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) s)) b alpha) =
      @TensorProduct.tmul ℤ inferInstance ℚ
        (BivariantClass (fun _ ↦ 0) (𝟙 Y) (s + r)) inferInstance
        (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) (s + r)).toAddCommMonoid
        inferInstance (@AddCommGroup.toIntModule _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 Y) (s + r))) (a * b)
        (BivariantClass.properPushforwardToTarget (fun _ ↦ 0)
          (Limits.prod.snd : X ⨯ Y ⟶ Y) (s + r)
          ((Category.id_comp (Limits.prod.snd : X ⨯ Y ⟶ Y)) ▸
            BivariantClass.comp (fun _ ↦ 0) (𝟙 (X ⨯ Y))
              (Limits.prod.snd : X ⨯ Y ⟶ Y)
              (BivariantClass.restrict (fun _ ↦ 0)
                (Limits.prod.fst : X ⨯ Y ⟶ X) (𝟙 (X ⨯ Y))
                (Limits.prod.fst : X ⨯ Y ⟶ X)
                (productFstIdentityIsPullback X Y) s alpha) c)) := sorry

/-- composition of rational Chow correspondences is
`ℚ`-linear in the first correspondence. -/
theorem composition_linear_left
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s : ℤ} (a b : ℚ) (c₁ c₂ : Rational X Y r) (d : Rational Y Z s) :
    composition X Y Z r s (a • c₁ + b • c₂) d =
      a • composition X Y Z r s c₁ d + b • composition X Y Z r s c₂ d := sorry

/-- composition of rational Chow correspondences is
`ℚ`-linear in the second correspondence. -/
theorem composition_linear_right
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s : ℤ} (a b : ℚ) (c : Rational X Y r) (d₁ d₂ : Rational Y Z s) :
    composition X Y Z r s c (a • d₁ + b • d₂) =
      a • composition X Y Z r s c d₁ + b • composition X Y Z r s c d₂ := sorry

/-- composition of rational Chow correspondences is associative,
after the named canonical transport of its grading. -/
theorem composition_assoc
    {X Y Z W : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    [Smooth W.hom] [Projective W.hom] {r s t : ℤ}
    (c : Rational X Y r) (d : Rational Y Z s) (e : Rational Z W t) :
    castDegree (add_assoc r s t)
        (composition X Z W (r + s) t (composition X Y Z r s c d) e) =
      composition X Y W r (s + t) c (composition Y Z W s t d e) := sorry

/-- The canonical identification `CH_(-r)(X) ⊗ ℚ ≃ₗ[ℚ] Corr^r(X, Spec k)`,
obtained from the Chow comparison and the cartesian comparison `X × Spec k ≅ X`. -/
noncomputable def homologyEquiv (X : SchemeOverField k) [Smooth X.hom]
    [Projective X.hom] (r : ℤ) :
    RationalChowHomology X (-r) ≃ₗ[ℚ] Rational X (SchemeOverField.point k) r :=
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ SchemeOverField.point k ⟶ SchemeOverField.point k) r
  let forward := fun alpha : RelativeChow (fun _ ↦ 0) X (-r) ↦
        BivariantClass.restrict (fun _ ↦ 0) Limits.prod.fst Limits.prod.snd
          (𝟙 (SchemeOverField.point k))
          (pointProductIsPullback X (𝟙 (SchemeOverField.point k))) r
          ((pointChowEquiv X r).invFun alpha)
  let inverse := fun c : Integral X (SchemeOverField.point k) r ↦
        pointChowEquiv X r
          (BivariantClass.properPushforward (fun _ ↦ 0)
            (Limits.prod.fst : X ⨯ SchemeOverField.point k ⟶ X)
            (terminal.from X) r (castHom (productFst_comp_toPoint X).symm r c))
  let integralEquiv := @AddEquiv.mk (RelativeChow (fun _ ↦ 0) X (-r))
    (Integral X (SchemeOverField.point k) r) inferInstance targetGroup.toAdd
    (@Equiv.mk _ _ forward inverse sorry sorry) sorry
  let forwardMap := (@AddEquiv.toIntLinearEquiv _ _ inferInstance targetGroup
    inferInstance (@AddCommGroup.toIntModule _ targetGroup) integralEquiv).toLinearMap
  let inverseEquiv := integralEquiv.symm
  let inverseMap := (@AddEquiv.toIntLinearEquiv _ _ targetGroup inferInstance
    (@AddCommGroup.toIntModule _ targetGroup) inferInstance inverseEquiv).toLinearMap
  { forwardMap.baseChange ℚ with
    invFun := inverseMap.baseChange ℚ
    left_inv := sorry
    right_inv := sorry }

/-- under `homologyEquiv`, the geometric pullback action of a
correspondence is composition with that correspondence. -/
theorem homologyEquiv_pullback
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] {r s : ℤ}
    (c : Rational X Y r) (alpha : RationalChowHomology Y (-s)) :
    homologyEquiv X (r + s) (pullback X Y r s c alpha) =
      composition X Y (SchemeOverField.point k) r s c (homologyEquiv Y s alpha) := sorry

/-- the canonical identification
`CH^r(X) ⊗ ℚ ≃ₗ[ℚ] Corr^r(Spec k, X)`, obtained by pulling operational
classes across the product comparison `Spec k × X ≅ X`. -/
noncomputable def cohomologyEquiv (X : SchemeOverField k) [Smooth X.hom]
    [Projective X.hom] (r : ℤ) :
    RationalChowCohomology X r ≃ₗ[ℚ] Rational (SchemeOverField.point k) X r :=
  let sourceGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r
  let targetGroup := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X) r
  let forward := fun c : BivariantClass (fun _ ↦ 0) (𝟙 X) r ↦
        BivariantClass.restrict (fun _ ↦ 0) Limits.prod.snd
          Limits.prod.snd (𝟙 X)
          (pointProductSndIsPullback X) r c
  let inverse := fun c : Integral (SchemeOverField.point k) X r ↦
        BivariantClass.properPushforwardToTarget (fun _ ↦ 0)
          (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X) r c
  let integralEquiv := @AddEquiv.mk (BivariantClass (fun _ ↦ 0) (𝟙 X) r)
    (Integral (SchemeOverField.point k) X r) sourceGroup.toAdd targetGroup.toAdd
    (@Equiv.mk _ _ forward inverse sorry sorry) sorry
  let forwardMap := (@AddEquiv.toIntLinearEquiv _ _ sourceGroup targetGroup
    (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ targetGroup)
    integralEquiv).toLinearMap
  let inverseEquiv := integralEquiv.symm
  let inverseMap := (@AddEquiv.toIntLinearEquiv _ _ targetGroup sourceGroup
    (@AddCommGroup.toIntModule _ targetGroup) (@AddCommGroup.toIntModule _ sourceGroup)
    inverseEquiv).toLinearMap
  { forwardMap.baseChange ℚ with
    invFun := inverseMap.baseChange ℚ
    left_inv := sorry
    right_inv := sorry }

/-- under `cohomologyEquiv`, the geometric pushforward action of a
correspondence is composition with that correspondence. -/
theorem cohomologyEquiv_pushforward
    {X Y : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] {r s : ℤ}
    (c : Rational X Y r) (alpha : RationalChowCohomology X s) :
    cohomologyEquiv Y (s + r) (pushforward X Y r s c alpha) =
      composition (SchemeOverField.point k) X Y s r (cohomologyEquiv X s alpha) c := sorry

/-- pullback of rational Chow cycles is compatible with
composition of correspondences: `(d ∘ c)⁺ α = c⁺ (d⁺ α)`. -/
theorem pullback_composition
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s t : ℤ} (c : Rational X Y r) (d : Rational Y Z s)
    (alpha : RationalChowHomology Z (-t)) :
    castHomologyDegree (congrArg Neg.neg (add_assoc r s t))
        (pullback X Z (r + s) t (composition X Y Z r s c d) alpha) =
      pullback X Y r (s + t) c (pullback Y Z s t d alpha) := sorry

/-- pushforward of rational Chow cycles is compatible with
composition of correspondences: `(d ∘ c)₍*₎ α = d₍*₎ (c₍*₎ α)`. -/
theorem pushforward_composition
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s t : ℤ} (c : Rational X Y r) (d : Rational Y Z s)
    (alpha : RationalChowCohomology X t) :
    castCohomologyDegree (add_assoc t r s).symm
        (pushforward X Z (r + s) t (composition X Y Z r s c d) alpha) =
      pushforward Y Z s (t + r) d (pushforward X Y r t c alpha) := sorry


end RationalConstructions

end AlgebraicGeometry.Correspondence
