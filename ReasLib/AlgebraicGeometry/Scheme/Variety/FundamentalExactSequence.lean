/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Units
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.EtaleOrders

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale.Small
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.MultiplicativeGroup

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
    (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
    AddCommGrpCat.{u}]

/-- The fibre-product projection `U ×_X η ⟶ U` on the small étale site. -/
def genericPullbackProjection :
    smallEtalePullback (genericPointInclusion X) ⋙
        smallEtaleToScheme (Spec (X.left.residueField (genericPoint X.left))) ⟶
      smallEtaleToScheme X.left where
  app U := pullback.fst U.hom (genericPointInclusion X)
  naturality _ _ _ := sorry

/-- The direct image of generic-fibre units on the small étale site of `X`. -/
def genericUnitsPushforward :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (genericPointInclusion X)).sheafPushforwardContinuous
      AddCommGrpCat.{u} X.left.smallEtaleTopology
      (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology).obj
    (unitsAddSheaf (Spec (X.left.residueField (genericPoint X.left))))

variable (x : X.left) (hx : x ∈ closedPoints X.left)
variable [HasSheafify (Spec (X.left.residueField x)).smallEtaleTopology AddCommGrpCat.{u}]

/-- The direct image of the constant integer sheaf at a closed point. -/
def closedPointConstantZPushforward :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (closedPointInclusion X x hx)).sheafPushforwardContinuous
      AddCommGrpCat.{u} X.left.smallEtaleTopology
      (Spec (X.left.residueField x)).smallEtaleTopology).obj
    ((constantSheaf (Spec (X.left.residueField x)).smallEtaleTopology
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))

variable [∀ x : ClosedPoint X,
    HasSheafify (Spec (X.left.residueField x.1)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproduct fun x : ClosedPoint X =>
    closedPointConstantZPushforward X x.1 x.2]

/-- The coproduct of all closed-point constant integer skyscraper sheaves. -/
def closedPointsCoproduct : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} :=
  ∐ fun x : ClosedPoint X => closedPointConstantZPushforward X x.1 x.2

/-- Restriction of units along the generic-point inclusion. -/
def unitsToGenericPushforward :
    unitsAddSheaf X.left ⟶ genericUnitsPushforward X :=
  ObjectProperty.homMk
    { app := fun U =>
        CommGrpCat.toAddCommGrp.map
          (unitsFunctor.map ((genericPullbackProjection X).app (unop U)).op)
      naturality := fun _ _ _ => sorry }

variable [IsLocallyNoetherian X.left]

/-- The local order morphism on an integral étale object. -/
noncomputable def integralOrderSection (U : X.left.Etale) [IsIntegral U.left]
    (x : ClosedPoint X) :
    (genericUnitsPushforward X).1.obj (op U) ⟶
      (closedPointConstantZPushforward X x.1 x.2).1.obj (op U) :=
  AddCommGrpCat.ofHom (EtaleOrders.fibreOrder X U x) ≫
    pointwiseConstantSection
      (hR := ⟨Field.toIsField (X.left.residueField x.1)⟩)
      ((smallEtalePullback (closedPointInclusion X x.1 x.2)).obj U)

/-- Local order morphisms are natural under restriction between integral objects. -/
theorem integralOrderSection_naturality {U V : X.left.Etale}
    [IsIntegral U.left] [IsIntegral V.left] (f : U ⟶ V) (x : ClosedPoint X) :
    (genericUnitsPushforward X).1.map f.op ≫
        integralOrderSection X U x =
      integralOrderSection X V x ≫
        (closedPointConstantZPushforward X x.1 x.2).1.map f.op := sorry

/-- The family of closed-point skyscraper sheaves indexed by closed points. -/
abbrev closedPointSkyscraperFamily : ClosedPoint X →
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} :=
  fun x => closedPointConstantZPushforward X x.1 x.2

/-- The finite local divisor morphism on an integral affine étale object. -/
noncomputable def affineDivisorSection (U : X.left.Etale)
    [IsIntegral U.left] [IsAffine U.left] :
    (genericUnitsPushforward X).1.obj (op U) ⟶
      (closedPointsCoproduct X).1.obj (op U) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun s =>
      let S := (EtaleOrders.fibreOrder_finite X U inferInstance s).toFinset
      ∑ x ∈ S,
        ((Sigma.ι (closedPointSkyscraperFamily X) x).hom.app (op U)).hom
          ((integralOrderSection X U x).hom s))
    (by sorry))

/-- Local divisor morphisms are natural on integral affine objects. -/
theorem affineDivisorSection_naturality {U V : X.left.Etale}
    [IsIntegral U.left] [IsIntegral V.left] [IsAffine U.left] [IsAffine V.left]
    (f : U ⟶ V) :
    (genericUnitsPushforward X).1.map f.op ≫ affineDivisorSection X U =
      affineDivisorSection X V ≫ (closedPointsCoproduct X).1.map f.op := sorry

/-- Compatibility of the local order family on arbitrary overlaps. -/
private theorem orderFamilyCompatible (U : X.left.Etale)
    (i j : EtaleOrders.IntegralAffineOpen X U) (x : ClosedPoint X) :
    ∀ ⦃W : X.left.Etale⦄ (a : W ⟶ i.toEtale) (b : W ⟶ j.toEtale),
      a ≫ i.inclusion = b ≫ j.inclusion →
        ((genericUnitsPushforward X).1.map i.inclusion.op ≫
          integralOrderSection X i.toEtale x) ≫
            (closedPointConstantZPushforward X x.1 x.2).1.map a.op =
          ((genericUnitsPushforward X).1.map j.inclusion.op ≫
            integralOrderSection X j.toEtale x) ≫
              (closedPointConstantZPushforward X x.1 x.2).1.map b.op := sorry

/-- Compatibility of the local divisor family on arbitrary overlaps. -/
private theorem divisorFamilyCompatible (U : X.left.Etale)
    (i j : EtaleOrders.IntegralAffineOpen X U) :
    ∀ ⦃W : X.left.Etale⦄ (a : W ⟶ i.toEtale) (b : W ⟶ j.toEtale),
      a ≫ i.inclusion = b ≫ j.inclusion →
        ((genericUnitsPushforward X).1.map i.inclusion.op ≫
          affineDivisorSection X i.toEtale) ≫ (closedPointsCoproduct X).1.map a.op =
          ((genericUnitsPushforward X).1.map j.inclusion.op ≫
            affineDivisorSection X j.toEtale) ≫ (closedPointsCoproduct X).1.map b.op := sorry

/-- The global order morphism obtained by descent from integral affine opens. -/
@[no_expose]
noncomputable def closedPointOrderMap (x : X.left) (hx : x ∈ closedPoints X.left)
    [HasSheafify (Spec (X.left.residueField x)).smallEtaleTopology AddCommGrpCat.{u}] :
    genericUnitsPushforward X ⟶ closedPointConstantZPushforward X x hx :=
  ObjectProperty.homMk
    { app := fun U =>
        (closedPointConstantZPushforward X x hx).property.amalgamateOfArrows
          (fun i : EtaleOrders.IntegralAffineOpen X (unop U) => i.inclusion)
          (EtaleOrders.integralAffineOpenCover X (unop U))
          (fun i =>
            (genericUnitsPushforward X).1.map i.inclusion.op ≫
              integralOrderSection X i.toEtale ⟨x, hx⟩)
          (fun {W i j} a b h => orderFamilyCompatible X (unop U) i j ⟨x, hx⟩ a b h)
      naturality := fun _ _ _ => sorry }

/-- The global divisor morphism obtained by descent from integral affine opens. -/
@[no_expose]
noncomputable def divisorRestriction :
    genericUnitsPushforward X ⟶ closedPointsCoproduct X :=
  ObjectProperty.homMk
    { app := fun U =>
        (closedPointsCoproduct X).property.amalgamateOfArrows
          (fun i : EtaleOrders.IntegralAffineOpen X (unop U) => i.inclusion)
          (EtaleOrders.integralAffineOpenCover X (unop U))
          (fun i =>
            (genericUnitsPushforward X).1.map i.inclusion.op ≫
              affineDivisorSection X i.toEtale)
          (fun {W i j} a b h => divisorFamilyCompatible X (unop U) i j a b h)
      naturality := fun _ _ _ => sorry }

/-- The global order map restricts to the local order map on integral affine objects. -/
theorem closedPointOrderMap_app_integralAffine {U : X.left.Etale}
    [IsIntegral U.left] [IsAffine U.left] (x : ClosedPoint X) :
    (closedPointOrderMap X x.1 x.2).hom.app (op U) = integralOrderSection X U x := sorry

/-- The global divisor map restricts to the finite local sum on integral affine objects. -/
theorem divisorRestriction_app_integralAffine {U : X.left.Etale}
    [IsIntegral U.left] [IsAffine U.left] :
    (divisorRestriction X).hom.app (op U) = affineDivisorSection X U := sorry

/-- The coproduct-to-product comparison for the closed-point family. -/
def closedPointsCoproductToProduct
    [HasProduct fun x : ClosedPoint X => closedPointConstantZPushforward X x.1 x.2] :
    closedPointsCoproduct X ⟶ Limits.piObj (closedPointSkyscraperFamily X) :=
  Sigma.desc fun b =>
    Pi.lift fun c =>
      @dite _ (b = c) (Classical.decEq _ b c)
        (fun h => eqToHom (congrArg (closedPointSkyscraperFamily X) h))
        (fun _ => 0)

/-- The two morphisms in the fundamental sequence compose to zero. -/
theorem unitsToGenericPushforward_comp_divisorRestriction :
    unitsToGenericPushforward X ≫ divisorRestriction X = 0 := sorry

/-- The canonical short complex of units, generic units, and closed-point orders. -/
def fundamentalShortComplex :
    ShortComplex (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) where
  f := unitsToGenericPushforward X
  g := divisorRestriction X
  zero := unitsToGenericPushforward_comp_divisorRestriction X

/-- The first object of the fundamental short complex is the units sheaf. -/
theorem fundamentalShortComplex_X₁ :
    (fundamentalShortComplex X).X₁ = unitsAddSheaf X.left := sorry

/-- The middle object of the fundamental short complex is the generic direct image. -/
theorem fundamentalShortComplex_X₂ :
    (fundamentalShortComplex X).X₂ = genericUnitsPushforward X := sorry

/-- The last object of the fundamental short complex is the closed-point coproduct. -/
theorem fundamentalShortComplex_X₃ :
    (fundamentalShortComplex X).X₃ = closedPointsCoproduct X := sorry

/-- The divisor morphism has the prescribed closed-point components. -/
theorem divisorRestriction_comp_π
    [HasProduct fun x : ClosedPoint X => closedPointConstantZPushforward X x.1 x.2]
    (x : ClosedPoint X) :
    divisorRestriction X ≫ closedPointsCoproductToProduct X ≫
        Pi.π (closedPointSkyscraperFamily X) x =
      closedPointOrderMap X x.1 x.2 := sorry

/-- The fundamental short complex is short exact. -/
theorem fundamentalExactSequence :
    (fundamentalShortComplex X).ShortExact := sorry

end AlgebraicGeometry.SchemeOverField
