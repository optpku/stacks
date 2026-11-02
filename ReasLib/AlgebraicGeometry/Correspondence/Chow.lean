/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.BivariantClass.OverField
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.Rationalization
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Finite
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
theorem point_locallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom :=
  SchemeOverField.instTerminalLocallyOfFiniteType

/-- The first product projection is proper when the second factor is proper over the field. -/
instance productFst_isProper (X Y : SchemeOverField k) [IsProper Y.hom] :
    IsProper (Limits.prod.fst : X ⨯ Y ⟶ X).left := by
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (Limits.prod.fst : X ⨯ Y ⟶ X) Limits.prod.snd)
      (prodIsProd X Y)).flip ‹IsProper Y.hom›

/-- The second product projection is proper when the first factor is proper over the field. -/
instance productSnd_isProper (X Y : SchemeOverField k) [IsProper X.hom] :
    IsProper (Limits.prod.snd : X ⨯ Y ⟶ Y).left := by
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (Limits.prod.fst : X ⨯ Y ⟶ X) Limits.prod.snd)
      (prodIsProd X Y)) ‹IsProper X.hom›

/-- Transport a bivariant class along equality of its underlying morphism. -/
def castHom {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {f g : X ⟶ Y} (h : f = g) (p : ℤ) :
    BivariantClass (fun _ ↦ 0) f p → BivariantClass (fun _ ↦ 0) g p :=
  fun c ↦ h ▸ c

/-- `castHom` is the direct transport along the supplied morphism equality. -/
theorem castHom_apply {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] {f g : X ⟶ Y} (h : f = g) (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) f p) : castHom h p c = h ▸ c := rfl

/-- Equality of cap families determines the class, independently of its compatibility proofs. -/
private theorem capFamily_ext {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} {c d : BivariantClass (fun _ ↦ 0) f p}
    (h : @c.cap = @d.cap) : c = d := by
  cases c
  cases d
  cases h
  rfl

private theorem castHom_pointwiseAdd {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f g : X ⟶ Y} (h : f = g) (p : ℤ) (c d : BivariantClass (fun _ ↦ 0) f p) :
    castHom h p (BivariantClass.pointwiseAdd (fun _ ↦ 0) f p c d) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) g p (castHom h p c) (castHom h p d) := by
  cases h
  rfl

private theorem restrict_pointwiseAdd {X Y X' Y' : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c d : BivariantClass (fun _ ↦ 0) f p) :
    BivariantClass.restrict (fun _ ↦ 0) i f' g square p
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) f p c d) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) f' p
        (BivariantClass.restrict (fun _ ↦ 0) i f' g square p c)
        (BivariantClass.restrict (fun _ ↦ 0) i f' g square p d) := by
  apply capFamily_ext
  rfl

private theorem comp_pointwiseAdd_left {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c d : BivariantClass (fun _ ↦ 0) f p) (e : BivariantClass (fun _ ↦ 0) g q) :
    BivariantClass.comp (fun _ ↦ 0) f g
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) f p c d) e =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) (f ≫ g) (p + q)
        (BivariantClass.comp (fun _ ↦ 0) f g c e)
        (BivariantClass.comp (fun _ ↦ 0) f g d e) := by
  apply capFamily_ext
  funext X' Z' _ _ i fg' h _ square n
  apply AddMonoidHom.ext
  intro alpha
  simp [BivariantClass.comp, BivariantClass.compCap, BivariantClass.pointwiseAdd]

private theorem comp_pointwiseAdd_right {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass (fun _ ↦ 0) f p) (d e : BivariantClass (fun _ ↦ 0) g q) :
    BivariantClass.comp (fun _ ↦ 0) f g c
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) g q d e) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) (f ≫ g) (p + q)
        (BivariantClass.comp (fun _ ↦ 0) f g c d)
        (BivariantClass.comp (fun _ ↦ 0) f g c e) := by
  apply capFamily_ext
  funext X' Z' _ _ i fg' h _ square n
  apply AddMonoidHom.ext
  intro alpha
  simp [BivariantClass.comp, BivariantClass.compCap, BivariantClass.pointwiseAdd]

private theorem properPushforward_pointwiseAdd {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ Z) (p : ℤ)
    (c d : BivariantClass (fun _ ↦ 0) (f ≫ g) p) :
    BivariantClass.properPushforward (fun _ ↦ 0) f g p
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) (f ≫ g) p c d) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) g p
        (BivariantClass.properPushforward (fun _ ↦ 0) f g p c)
        (BivariantClass.properPushforward (fun _ ↦ 0) f g p d) := by
  apply capFamily_ext
  funext Y' Z' _ _ i g' h _ square n
  apply AddMonoidHom.ext
  intro alpha
  simp [BivariantClass.properPushforward, BivariantClass.properPushforwardCap,
    BivariantClass.pointwiseAdd]

private theorem properPushforwardToTarget_pointwiseAdd {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (p : ℤ) (c d : BivariantClass (fun _ ↦ 0) f p) :
    BivariantClass.properPushforwardToTarget (fun _ ↦ 0) f p
        (BivariantClass.pointwiseAdd (fun _ ↦ 0) f p c d) =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 Y) p
        (BivariantClass.properPushforwardToTarget (fun _ ↦ 0) f p c)
        (BivariantClass.properPushforwardToTarget (fun _ ↦ 0) f p d) := by
  apply capFamily_ext
  funext Y' Z' _ _ i g' h _ square n
  apply AddMonoidHom.ext
  intro alpha
  simp [BivariantClass.properPushforwardToTarget, BivariantClass.properPushforward,
    BivariantClass.properPushforwardCap, BivariantClass.pointwiseAdd]

/-- The product projections over a field form a pullback square against maps to its point. -/
theorem pointProductIsPullback (X : SchemeOverField k) {Y : SchemeOverField k}
    (g : Y ⟶ SchemeOverField.point k) :
    IsPullback (Limits.prod.fst : X ⨯ Y ⟶ X).left
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left (terminal.from X).left g.left :=
  SchemeOverField.productIsPullback X g

/-- The canonical pullback comparison with `X ⨯ Y` respects the structure maps. -/
theorem pointProductIso_hom_base
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (square.isoIsPullback X.left Y.left (pointProductIsPullback X g)).hom ≫
        (X ⨯ Y).hom = X'.hom :=
  SchemeOverField.productIsoOfIsPullback_hom_base X i f' g square

/- The following complete Prop certificates preserve the names and binder lists
recorded by compiled clients of the former comparison implementation. They reuse the
chosen limits, and introduce neither product data nor competing instances. -/
theorem pointProductIso._proof_1 : HasTerminal (Over (Spec (CommRingCat.of k))) :=
  Over.instHasTerminal

theorem pointProductIso._proof_2 (X : SchemeOverField k) {Y : SchemeOverField k} :
    HasLimit (pair X Y) := hasLimitOfHasLimitsOfShape (pair X Y)

/-- The canonical isomorphism from a cartesian representative over the point to a product. -/
noncomputable def pointProductIso
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    X' ≅ X ⨯ Y :=
  SchemeOverField.productIsoOfIsPullback X i f' g square

/-- The point-product comparison followed by the first projection is the given map. -/
theorem pointProductIso_hom_fst
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ SchemeOverField.point k)
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (pointProductIso X i f' g square).hom ≫ Limits.prod.fst = i := by
  apply Over.OverMorphism.ext
  change (SchemeOverField.productIsoOfIsPullback X i f' g square).hom.left ≫
    (Limits.prod.fst : X ⨯ Y ⟶ X).left = i.left
  rw [SchemeOverField.productIsoOfIsPullback_hom_left]
  exact square.isoIsPullback_hom_fst _ _ (pointProductIsPullback X g)

/-- The degree-zero fundamental Chow class of the spectrum of the ground field. -/
noncomputable def pointFundamentalClass (k : Type u) [Field k] :
    RelativeChow (fun _ ↦ 0) (SchemeOverField.point k) 0 :=
  ChowGroup.specFundamentalClass k

/-- The point fundamental class is represented by its degree-zero fundamental cycle. -/
theorem pointFundamentalClass_def (k : Type u) [Field k] :
    pointFundamentalClass k =
      @chowClass (SchemeOverField.point k).left
        (LocallyOfFiniteType.isLocallyNoetherian (SchemeOverField.point k).hom)
        ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0))
        inferInstance 0
        (@CycleGroup.fundamental (SchemeOverField.point k).left
          (LocallyOfFiniteType.isLocallyNoetherian (SchemeOverField.point k).hom)
          ((SchemeOverField.point k).hom.relativeDimensionFunction (fun _ ↦ 0)) 0) := rfl

/-! The point-Chow names below are compatibility facades for `BivariantClass.OverField`.
The field owner supplies all six maps, the product comparison, and the point fundamental
class. These aliases preserve the historical correspondence API without new instances. -/

/-- Compatibility facade for the field owner's exterior-product cap family. -/
noncomputable def ofChowCap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CapFamily (fun _ ↦ 0) (terminal.from X) p :=
  BivariantClass.ofChowCap X p alpha

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
        (RelativeChow.castDegree (fun _ ↦ 0) (neg_add_eq_sub p n)
          (ChowGroup.exteriorProductPairing X Y' (-p) n alpha beta)) := rfl

/-- Exterior-product cap families commute with proper pushforward. -/
theorem ofChowCap_mapProper (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithProperPushforward (fun _ ↦ 0)
      (ofChowCap X p alpha) :=
  BivariantClass.ofChowCap_mapProper X p alpha

/-- Exterior-product cap families commute with flat pullback. -/
theorem ofChowCap_pullbackFlat (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithFlatPullback (fun _ ↦ 0)
      (ofChowCap X p alpha) :=
  BivariantClass.ofChowCap_pullbackFlat X p alpha

/-- Exterior-product cap families commute with effective-Cartier Gysin pullback. -/
theorem ofChowCap_gysinCartier (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass.CompatibleWithCartierGysin (fun _ ↦ 0)
      (ofChowCap X p alpha) :=
  BivariantClass.ofChowCap_gysinCartier X p alpha

/-- The bivariant class whose action is exterior product with a Chow class. -/
noncomputable def ofChowClass (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass (fun _ ↦ 0) (terminal.from X) p :=
  BivariantClass.ofChowClass X p alpha

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
      ofChowCap X p alpha i f' g square n beta := rfl

section PointComparison

/-- Exterior product defines an additive map from Chow classes to bivariant classes. -/
noncomputable def ofChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  BivariantClass.ofChow X p

/-- The additive map `ofChow` sends a class to its exterior-product bivariant class. -/
theorem ofChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChow X p alpha = ofChowClass X p alpha := rfl

/-- Evaluation of a bivariant class on the fundamental class of the field point. -/
noncomputable def toChowValue (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    RelativeChow (fun _ ↦ 0) X (-p) :=
  BivariantClass.toChowValue X p c

/-- Evaluation on the field point is the formal cap product with its fundamental class. -/
theorem toChowValue_def (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p c =
      RelativeChow.castDegree (fun _ ↦ 0) (zero_sub p)
        (c.cap (𝟙 X) (terminal.from X) (𝟙 (SchemeOverField.point k))
          IsPullback.of_id_fst 0 (pointFundamentalClass k)) := rfl

/-- Evaluation on the field point as an additive map. -/
noncomputable def toChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  BivariantClass.toChow X p

/-- The additive map `toChow` evaluates on the field-point fundamental class. -/
theorem toChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChow X p c = toChowValue X p c := rfl

/-- The canonical additive identification of Chow classes with bivariant classes over
the field point. -/
noncomputable def pointChowEquiv (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :=
  BivariantClass.chowEquiv X p

/-- The forward map of `pointChowEquiv` is evaluation on the field point. -/
theorem pointChowEquiv_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    pointChowEquiv X p c = toChow X p c := rfl

end PointComparison

/-- Historical binary-product certificate for the integral carrier. -/
theorem Integral._proof_1 (X Y : SchemeOverField k) : HasLimit (pair X Y) :=
  hasLimitOfHasLimitsOfShape (pair X Y)

/-- Historical product finite-type certificate for the integral carrier. -/
theorem Integral._proof_2 (X Y : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⨯ Y).hom :=
  locallyOfFiniteType_overProd X Y

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
    LocallyOfFiniteType (CompositionSpace X Y Z).hom := by
  haveI : LocallyOfFiniteType (Limits.prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback
      (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (Limits.prod.fst : X ⨯ Y ⟶ X) Limits.prod.snd)
        (prodIsProd X Y)) ‹LocallyOfFiniteType X.hom›
  haveI : LocallyOfFiniteType
      (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).map (Over.forget _))
      ‹LocallyOfFiniteType (Limits.prod.snd : X ⨯ Y ⟶ Y).left›
  rw [← (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
    (Limits.prod.fst : Y ⨯ Z ⟶ Y)).w]
  infer_instance

/-- The underlying square defining the correspondence-composition space is cartesian. -/
theorem composition_isPullback (X Y Z : SchemeOverField k) :
    IsPullback
      (pullback.fst (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).left
      (pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y)).left
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.fst : Y ⨯ Z ⟶ Y).left := by
  exact (IsPullback.of_hasPullback (Limits.prod.snd : X ⨯ Y ⟶ Y)
    (Limits.prod.fst : Y ⨯ Z ⟶ Y)).map (Over.forget _)

/-- The first projection from a product is locally of finite type when its
second factor is locally of finite type over the field. -/
instance productFst_locallyOfFiniteType (Y Z : SchemeOverField k)
    [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (Limits.prod.fst : Y ⨯ Z ⟶ Y).left := by
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (Limits.prod.fst : Y ⨯ Z ⟶ Y) Limits.prod.snd)
      (prodIsProd Y Z)).flip ‹LocallyOfFiniteType Z.hom›

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
    IsProper (compositionProjection X Y Z).left := by
  let middle : CompositionSpace X Y Z ⟶ Y :=
    pullback.fst (Limits.prod.snd : X ⨯ Y ⟶ Y)
      (Limits.prod.fst : Y ⨯ Z ⟶ Y) ≫ Limits.prod.snd
  have hlimit : IsLimit (BinaryFan.mk (compositionProjection X Y Z) middle) := by
    refine BinaryFan.isLimitMk
      (fun t ↦ pullback.lift
        (Limits.prod.lift (t.fst ≫ Limits.prod.fst) t.snd)
        (Limits.prod.lift t.snd (t.fst ≫ Limits.prod.snd)) (by
          rw [Limits.prod.lift_snd, Limits.prod.lift_fst])) ?_ ?_ ?_
    · intro t
      apply Limits.prod.hom_ext <;>
        simp only [compositionProjection, Limits.prod.lift_fst, Limits.prod.lift_snd,
          Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] <;> rfl
    · intro t
      simp only [middle, pullback.lift_fst_assoc, Limits.prod.lift_snd]
    · intro t m hm₁ hm₂
      apply pullback.hom_ext
      · apply Limits.prod.hom_ext
        · simpa only [compositionProjection, Category.assoc, Limits.prod.lift_fst,
            Limits.prod.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using!
            congrArg (fun f ↦ f ≫ Limits.prod.fst) hm₁
        · simpa only [middle, Category.assoc, Limits.prod.lift_snd,
            pullback.lift_fst_assoc] using! hm₂
      · apply Limits.prod.hom_ext
        · simpa only [middle, Category.assoc, Limits.prod.lift_fst,
            pullback.lift_snd_assoc, pullback.lift_fst_assoc, Limits.prod.lift_snd,
            ← pullback.condition] using! hm₂
        · simpa only [compositionProjection, Category.assoc, Limits.prod.lift_fst,
            Limits.prod.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using!
            congrArg (fun f ↦ f ≫ Limits.prod.snd) hm₁
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ hlimit).flip
    (inferInstance : IsProper Y.hom)

/-- The projection to `Z` through `X ⨯ Z` agrees with the projection through
`Y ⨯ Z`. -/
theorem compositionProjection_snd (X Y Z : SchemeOverField k) :
    compositionProjection X Y Z ≫ (Limits.prod.snd : X ⨯ Z ⟶ Z) =
      pullback.snd (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.fst : Y ⨯ Z ⟶ Y) ≫ (Limits.prod.snd : Y ⨯ Z ⟶ Z) := by
  exact Limits.prod.lift_snd _ _

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
        (integralCompositionValue X Y Z c d₂) := by
  simp only [integralCompositionValue, comp_pointwiseAdd_right, ← castHom_apply,
    castHom_pointwiseAdd, properPushforward_pointwiseAdd]

/-- Integral correspondence composition respects integer scaling in its second variable. -/
theorem integralCompositionValue_zsmul_right
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (c : Integral X Y r) (n : ℤ) (d : Integral Y Z s) :
    integralCompositionValue X Y Z c
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd s d n) =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionValue X Y Z c d) n := by
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : Y ⨯ Z ⟶ Z) s
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
  let f : Integral Y Z s →+ Integral X Z (r + s) :=
    AddMonoidHom.mk' (integralCompositionValue X Y Z c)
      (integralCompositionValue_add_right X Y Z c)
  exact map_zsmul f n d

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
        (integralCompositionRight X Y Z c₂ d) := by
  change integralCompositionValue X Y Z
    (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r c₁ c₂) d =
      BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionValue X Y Z c₁ d) (integralCompositionValue X Y Z c₂ d)
  simp only [integralCompositionValue, restrict_pointwiseAdd, comp_pointwiseAdd_left,
    ← castHom_apply, castHom_pointwiseAdd, properPushforward_pointwiseAdd]

/-- Integral correspondence composition respects integer scaling in its first variable. -/
theorem integralCompositionRight_zsmul
    (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [AlgebraicGeometry.Projective Y.hom]
    {r s : ℤ} (n : ℤ) (c : Integral X Y r) (d : Integral Y Z s) :
    integralCompositionRight X Y Z
        (BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd r c n) d =
      BivariantClass.pointwiseZsmul (fun _ ↦ 0) Limits.prod.snd (r + s)
        (integralCompositionRight X Y Z c d) n := by
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Z ⟶ Z) (r + s)
  let f : Integral X Y r →+ Integral X Z (r + s) :=
    AddMonoidHom.mk' (fun c ↦ integralCompositionRight X Y Z c d)
      (fun c₁ c₂ ↦ integralCompositionRight_add X Y Z c₁ c₂ d)
  exact map_zsmul f n c

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
        (a * b) (integralCompositionValue X Y Z c d) := by
  simp [composition, integralComposition, LinearMap.baseChange₂, TensorProduct.smul_tmul', smul_eq_mul]

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
          (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h)) c := rfl

/-- Transport rational Chow homology along an equality of homological degrees. -/
def castHomologyDegree {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {m n : ℤ} (h : m = n) :
    RationalChowHomology X m →ₗ[ℚ] RationalChowHomology X n :=
  (RelativeChow.castDegree (fun _ ↦ 0) h).toIntLinearMap.baseChange ℚ

/-- Homological grading transport is scalar extension of integral grading transport. -/
theorem castHomologyDegree_apply {X : SchemeOverField k} [LocallyOfFiniteType X.hom]
    {m n : ℤ} (h : m = n) (alpha : RationalChowHomology X m) :
    castHomologyDegree h alpha =
      (RelativeChow.castDegree (fun _ ↦ 0) h).toIntLinearMap.baseChange ℚ alpha := rfl

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
          (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) h)) alpha := rfl

/-- Rational grading transport is transport along equality of degrees. -/
theorem castDegree_eq_transport {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r s : ℤ} (h : r = s) (c : Rational X Y r) : castDegree h c = h ▸ c := by
  cases h
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r
  change castDegree (rfl : r = r) c = c
  induction c using TensorProduct.induction_on with
  | zero => exact (castDegree rfl).map_zero
  | tmul a c => simp [castDegree, BivariantClass.Nonnegative.castGrading]
  | add c d hc hd => simp only [map_add, hc, hd]

/-- Transport followed by its inverse cancels. -/
theorem castDegree_symm_apply_apply {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r s : ℤ} (h : r = s) (c : Rational X Y r) :
    castDegree h.symm (castDegree h c) = c := by
  cases h
  simp only [castDegree_eq_transport]

/-- Grading transport along reflexivity fixes every rational correspondence. -/
theorem castDegree_rfl {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r : ℤ} (c : Rational X Y r) : castDegree rfl c = c :=
  castDegree_eq_transport rfl c

/-- Successive grading transports compose. -/
theorem castDegree_trans {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r s t : ℤ} (h : r = s) (h' : s = t) (c : Rational X Y r) :
    castDegree h' (castDegree h c) = castDegree (h.trans h') c := by
  cases h
  cases h'
  simp only [castDegree_eq_transport]

/-- Composition commutes with transport of the two grading indices. -/
theorem composition_castDegree {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] [Projective Y.hom]
    {r r' s s' : ℤ} (hr : r = r') (hs : s = s')
    (f : Rational X Y r) (g : Rational Y Z s) :
    composition X Y Z r' s' (castDegree hr f) (castDegree hs g) =
      castDegree (congrArg₂ (· + ·) hr hs) (composition X Y Z r s f g) := by
  cases hr
  cases hs
  simp only [castDegree_eq_transport]

private theorem castHomologyDegree_eq_transport {X : SchemeOverField k}
    [LocallyOfFiniteType X.hom] {m n : ℤ} (h : m = n) (alpha : RationalChowHomology X m) :
    castHomologyDegree h alpha = h ▸ alpha := by
  cases h
  change castHomologyDegree (rfl : m = m) alpha = alpha
  induction alpha using TensorProduct.induction_on with
  | zero => exact (castHomologyDegree rfl).map_zero
  | tmul a alpha =>
      simp [castHomologyDegree, RelativeChow.castDegree, ChowGroup.reindex, AddEquiv.cast]
  | add alpha beta hα hβ => simp only [map_add, hα, hβ]

private theorem castCohomologyDegree_eq_transport {X : SchemeOverField k}
    [LocallyOfFiniteType X.hom] {r s : ℤ} (h : r = s) (alpha : RationalChowCohomology X r) :
    castCohomologyDegree h alpha = h ▸ alpha := by
  cases h
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (𝟙 X) r
  change castCohomologyDegree (rfl : r = r) alpha = alpha
  induction alpha using TensorProduct.induction_on with
  | zero => exact (castCohomologyDegree rfl).map_zero
  | tmul a alpha => simp [castCohomologyDegree, BivariantClass.Nonnegative.castGrading]
  | add alpha beta hα hβ => simp only [map_add, hα, hβ]

/-- The product projection followed by the structure map is the projection to the point. -/
theorem productFst_comp_toPoint (X : SchemeOverField k) :
    (Limits.prod.fst : X ⨯ SchemeOverField.point k ⟶ X) ≫ terminal.from X =
      (Limits.prod.snd : X ⨯ SchemeOverField.point k ⟶ SchemeOverField.point k) := by
  exact terminal.hom_ext _ _

/-- Pulling the identity of `X` back along the second projection from
`Spec k × X` gives the cartesian square presenting that projection. -/
theorem pointProductSndIsPullback (X : SchemeOverField k) :
    IsPullback
      (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X).left
      (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X).left
      (𝟙 X : X ⟶ X).left
      (𝟙 X : X ⟶ X).left := by
  haveI : IsIso (Limits.prod.snd : SchemeOverField.point k ⨯ X ⟶ X).left := by
    change IsIso ((Over.forget _).map (Limits.prod.leftUnitor X).hom)
    infer_instance
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Pulling the identity of `X` back along the first projection from `X × Y`
gives the cartesian square presenting that projection. -/
theorem productFstIdentityIsPullback (X Y : SchemeOverField k) :
    IsPullback
      (Limits.prod.fst : X ⨯ Y ⟶ X).left
      (𝟙 (X ⨯ Y) : X ⨯ Y ⟶ X ⨯ Y).left
      (𝟙 X : X ⟶ X).left
      (Limits.prod.fst : X ⨯ Y ⟶ X).left := by
  exact IsPullback.of_id_snd

/-- The grading identity for the action of a degree-`r` correspondence on
homological degree `-s`. -/
theorem pullbackDegree (r s : ℤ) : -s - r = -(r + s) := by
  simp [sub_eq_add_neg, add_comm]

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
      (RelativeChow.castDegree (fun _ ↦ 0) (pullbackDegree r s)
        (c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y) IsPullback.of_id_fst (-s) alpha))
  let integralPullback := @LinearMap.mk₂ ℤ inferInstance (Integral X Y r)
    (RelativeChow (fun _ ↦ 0) Y (-s)) (RelativeChow (fun _ ↦ 0) X (-(r + s)))
    sourceGroup.toAddCommMonoid inferInstance inferInstance
    (@AddCommGroup.toIntModule _ sourceGroup) inferInstance inferInstance integralValue
    (by
      intro c d alpha
      change integralValue (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r c d)
        alpha = integralValue c alpha + integralValue d alpha
      simp [integralValue, BivariantClass.pointwiseAdd])
    (by
      intro n c alpha
      letI := sourceGroup
      let f : Integral X Y r →+ RelativeChow (fun _ ↦ 0) X (-(r + s)) :=
        AddMonoidHom.mk' (fun d ↦ integralValue d alpha) (by
          intro d e
          change integralValue
            (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r d e) alpha = _
          simp [integralValue, BivariantClass.pointwiseAdd])
      exact map_zsmul f n c)
    (by
      intro c alpha beta
      simp [integralValue])
    (by
      intro n c alpha
      simpa [integralValue] using
        map_zsmul
          ((ChowGroup.map (fun _ ↦ 0) (X ⨯ Y) X Limits.prod.fst (-(r + s))).comp
            ((RelativeChow.castDegree (fun _ ↦ 0) (pullbackDegree r s)).comp
              (c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y)
                IsPullback.of_id_fst (-s)))) n alpha)
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
          (RelativeChow.castDegree (fun _ ↦ 0) (pullbackDegree r s)
            (c.cap (𝟙 (X ⨯ Y)) Limits.prod.snd (𝟙 Y)
              IsPullback.of_id_fst (-s) alpha)) := by
  simp [pullback, LinearMap.baseChange₂, TensorProduct.smul_tmul', smul_eq_mul]

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
    (@AddCommGroup.toIntModule _ targetGroup) integralValue
    (by
      intro c d alpha
      change integralValue (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r c d)
        alpha = BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 Y) (s + r)
          (integralValue c alpha) (integralValue d alpha)
      simp only [integralValue, comp_pointwiseAdd_right]
      exact properPushforwardToTarget_pointwiseAdd _ _ _ _)
    (by
      intro n c alpha
      letI := sourceGroup
      letI := targetGroup
      let f : Integral X Y r →+ BivariantClass (fun _ ↦ 0) (𝟙 Y) (s + r) :=
        AddMonoidHom.mk' (fun d ↦ integralValue d alpha) (by
          intro d e
          change integralValue
            (BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r d e) alpha =
              BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 Y) (s + r)
                (integralValue d alpha) (integralValue e alpha)
          simp only [integralValue, comp_pointwiseAdd_right]
          exact properPushforwardToTarget_pointwiseAdd _ _ _ _)
      exact map_zsmul f n c)
    (by
      intro c alpha beta
      change integralValue c (BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 X) s alpha beta) =
        BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 Y) (s + r)
          (integralValue c alpha) (integralValue c beta)
      simp only [integralValue, restrict_pointwiseAdd, comp_pointwiseAdd_left]
      exact properPushforwardToTarget_pointwiseAdd _ _ _ _)
    (by
      intro n c alpha
      letI := middleGroup
      letI := targetGroup
      let f : BivariantClass (fun _ ↦ 0) (𝟙 X) s →+
          BivariantClass (fun _ ↦ 0) (𝟙 Y) (s + r) :=
        AddMonoidHom.mk' (integralValue c) (by
          intro beta gamma
          change integralValue c
            (BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 X) s beta gamma) =
              BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 Y) (s + r)
                (integralValue c beta) (integralValue c gamma)
          simp only [integralValue, restrict_pointwiseAdd, comp_pointwiseAdd_left]
          exact properPushforwardToTarget_pointwiseAdd _ _ _ _)
      exact map_zsmul f n alpha)
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
                (productFstIdentityIsPullback X Y) s alpha) c)) := by
  simp [pushforward, LinearMap.baseChange₂, TensorProduct.smul_tmul', smul_eq_mul]

/-- composition of rational Chow correspondences is
`ℚ`-linear in the first correspondence. -/
theorem composition_linear_left
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s : ℤ} (a b : ℚ) (c₁ c₂ : Rational X Y r) (d : Rational Y Z s) :
    composition X Y Z r s (a • c₁ + b • c₂) d =
      a • composition X Y Z r s c₁ d + b • composition X Y Z r s c₂ d := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

/-- composition of rational Chow correspondences is
`ℚ`-linear in the second correspondence. -/
theorem composition_linear_right
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s : ℤ} (a b : ℚ) (c : Rational X Y r) (d₁ d₂ : Rational Y Z s) :
    composition X Y Z r s c (a • d₁ + b • d₂) =
      a • composition X Y Z r s c d₁ + b • composition X Y Z r s c d₂ := by
  simp only [map_add, map_smul]

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
          ((BivariantClass.chowEquiv X r).invFun alpha)
  let inverse := fun c : Integral X (SchemeOverField.point k) r ↦
        BivariantClass.chowEquiv X r
          (BivariantClass.properPushforward (fun _ ↦ 0)
            (Limits.prod.fst : X ⨯ SchemeOverField.point k ⟶ X)
            (terminal.from X) r (castHom (productFst_comp_toPoint X).symm r c))
  let integralEquiv := @AddEquiv.mk (RelativeChow (fun _ ↦ 0) X (-r))
    (Integral X (SchemeOverField.point k) r) inferInstance targetGroup.toAdd
    (@Equiv.mk _ _ forward inverse sorry sorry) (by
      intro alpha beta
      letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) r
      have h : (BivariantClass.chowEquiv X r).invFun (alpha + beta) =
          BivariantClass.pointwiseAdd (fun _ ↦ 0) (terminal.from X) r
            ((BivariantClass.chowEquiv X r).invFun alpha) ((BivariantClass.chowEquiv X r).invFun beta) :=
        (BivariantClass.ofChow X r).map_add alpha beta
      change forward (alpha + beta) =
        BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r (forward alpha) (forward beta)
      simp only [forward, h]
      exact restrict_pointwiseAdd _ _ _ _ _ _ _)
  let forwardMap := (@AddEquiv.toIntLinearEquiv _ _ inferInstance targetGroup
    inferInstance (@AddCommGroup.toIntModule _ targetGroup) integralEquiv).toLinearMap
  let inverseEquiv := integralEquiv.symm
  let inverseMap := (@AddEquiv.toIntLinearEquiv _ _ targetGroup inferInstance
    (@AddCommGroup.toIntModule _ targetGroup) inferInstance inverseEquiv).toLinearMap
  { forwardMap.baseChange ℚ with
    invFun := inverseMap.baseChange ℚ
    left_inv := by
      letI := targetGroup
      intro alpha
      change inverseMap.baseChange ℚ (forwardMap.baseChange ℚ alpha) = alpha
      induction alpha using TensorProduct.induction_on with
      | zero =>
          exact (congrArg (inverseMap.baseChange ℚ)
            (forwardMap.baseChange ℚ).map_zero).trans (inverseMap.baseChange ℚ).map_zero
      | tmul a alpha =>
          change inverseMap.baseChange ℚ (forwardMap.baseChange ℚ (a ⊗ₜ[ℤ] alpha)) = _
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
          exact congrArg (fun beta ↦ a ⊗ₜ[ℤ] beta) (integralEquiv.left_inv alpha)
      | add alpha beta hα hβ => simp only [map_add, hα, hβ]
    right_inv := by
      letI := targetGroup
      intro alpha
      change forwardMap.baseChange ℚ (inverseMap.baseChange ℚ alpha) = alpha
      induction alpha using TensorProduct.induction_on with
      | zero =>
          exact (congrArg (forwardMap.baseChange ℚ)
            (inverseMap.baseChange ℚ).map_zero).trans (forwardMap.baseChange ℚ).map_zero
      | tmul a alpha =>
          change forwardMap.baseChange ℚ (inverseMap.baseChange ℚ (a ⊗ₜ[ℤ] alpha)) = _
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
          exact congrArg (fun beta ↦ a ⊗ₜ[ℤ] beta) (integralEquiv.right_inv alpha)
      | add alpha beta hα hβ => simp only [map_add, hα, hβ] }

private theorem homologyEquiv_cast (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] {r s : ℤ} (h : r = s)
    (alpha : RationalChowHomology X (-r)) :
    homologyEquiv X s (castHomologyDegree (congrArg Neg.neg h) alpha) =
      castDegree h (homologyEquiv X r alpha) := by
  cases h
  simp only [castHomologyDegree_eq_transport, castDegree_eq_transport]

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
    (@Equiv.mk _ _ forward inverse sorry sorry) (by
      intro c d
      change forward (BivariantClass.pointwiseAdd (fun _ ↦ 0) (𝟙 X) r c d) =
        BivariantClass.pointwiseAdd (fun _ ↦ 0) Limits.prod.snd r (forward c) (forward d)
      exact restrict_pointwiseAdd _ _ _ _ _ c d)
  let forwardMap := (@AddEquiv.toIntLinearEquiv _ _ sourceGroup targetGroup
    (@AddCommGroup.toIntModule _ sourceGroup) (@AddCommGroup.toIntModule _ targetGroup)
    integralEquiv).toLinearMap
  let inverseEquiv := integralEquiv.symm
  let inverseMap := (@AddEquiv.toIntLinearEquiv _ _ targetGroup sourceGroup
    (@AddCommGroup.toIntModule _ targetGroup) (@AddCommGroup.toIntModule _ sourceGroup)
    inverseEquiv).toLinearMap
  { forwardMap.baseChange ℚ with
    invFun := inverseMap.baseChange ℚ
    left_inv := by
      letI := sourceGroup
      letI := targetGroup
      intro alpha
      change inverseMap.baseChange ℚ (forwardMap.baseChange ℚ alpha) = alpha
      induction alpha using TensorProduct.induction_on with
      | zero =>
          exact (congrArg (inverseMap.baseChange ℚ)
            (forwardMap.baseChange ℚ).map_zero).trans (inverseMap.baseChange ℚ).map_zero
      | tmul a alpha =>
          change inverseMap.baseChange ℚ (forwardMap.baseChange ℚ (a ⊗ₜ[ℤ] alpha)) = _
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
          exact congrArg (fun beta ↦ a ⊗ₜ[ℤ] beta) (integralEquiv.left_inv alpha)
      | add alpha beta hα hβ => simp only [map_add, hα, hβ]
    right_inv := by
      letI := sourceGroup
      letI := targetGroup
      intro alpha
      change forwardMap.baseChange ℚ (inverseMap.baseChange ℚ alpha) = alpha
      induction alpha using TensorProduct.induction_on with
      | zero =>
          exact (congrArg (forwardMap.baseChange ℚ)
            (inverseMap.baseChange ℚ).map_zero).trans (forwardMap.baseChange ℚ).map_zero
      | tmul a alpha =>
          change forwardMap.baseChange ℚ (inverseMap.baseChange ℚ (a ⊗ₜ[ℤ] alpha)) = _
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
          exact congrArg (fun beta ↦ a ⊗ₜ[ℤ] beta) (integralEquiv.right_inv alpha)
      | add alpha beta hα hβ => simp only [map_add, hα, hβ] }

private theorem cohomologyEquiv_cast (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] {r s : ℤ} (h : r = s)
    (alpha : RationalChowCohomology X r) :
    cohomologyEquiv X s (castCohomologyDegree h alpha) =
      castDegree h (cohomologyEquiv X r alpha) := by
  cases h
  simp only [castCohomologyDegree_eq_transport, castDegree_eq_transport]

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
      pullback X Y r (s + t) c (pullback Y Z s t d alpha) := by
  apply (homologyEquiv X (r + (s + t))).injective
  calc
    _ = castDegree (add_assoc r s t)
        (homologyEquiv X ((r + s) + t)
          (pullback X Z (r + s) t (composition X Y Z r s c d) alpha)) :=
      homologyEquiv_cast X (add_assoc r s t) _
    _ = _ := by
      simpa only [homologyEquiv_pullback] using
        (composition_assoc c d (homologyEquiv Z t alpha))

/-- pushforward of rational Chow cycles is compatible with
composition of correspondences: `(d ∘ c)₍*₎ α = d₍*₎ (c₍*₎ α)`. -/
theorem pushforward_composition
    {X Y Z : SchemeOverField k} [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] [Smooth Z.hom] [Projective Z.hom]
    {r s t : ℤ} (c : Rational X Y r) (d : Rational Y Z s)
    (alpha : RationalChowCohomology X t) :
    castCohomologyDegree (add_assoc t r s).symm
        (pushforward X Z (r + s) t (composition X Y Z r s c d) alpha) =
      pushforward Y Z s (t + r) d (pushforward X Y r t c alpha) := by
  apply (cohomologyEquiv Z ((t + r) + s)).injective
  simp only [cohomologyEquiv_cast, cohomologyEquiv_pushforward]
  have h := congrArg (castDegree (add_assoc t r s).symm)
    (composition_assoc (cohomologyEquiv X t alpha) c d)
  simpa only [castDegree_symm_apply_apply] using h.symm


end RationalConstructions

end AlgebraicGeometry.Correspondence
