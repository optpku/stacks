/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Units
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale.Small
open CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom]

/-- The canonical morphism from the generic point of a curve to its underlying scheme. -/
def genericPointInclusion :
    Spec (X.left.residueField (genericPoint X.left)) ⟶ X.left :=
  X.left.fromSpecResidueField (genericPoint X.left)

/-- The canonical morphism from the residue field of a closed point to the curve. -/
def closedPointInclusion (x : X.left) (hx : x ∈ closedPoints X.left) :
    Spec (X.left.residueField x) ⟶ X.left :=
  X.left.fromSpecResidueField x

/-- The type of closed points of the underlying scheme of `X`. -/
abbrev ClosedPoint := {x : X.left // x ∈ closedPoints X.left}

namespace EtaleOrders

/-- An integral affine open of an étale object over `X`. -/
abbrev IntegralAffineOpen (U : X.left.Etale) :=
  {V : U.left.affineOpens // IsIntegral (V : Scheme)}

/-- The integrality property stored by an integral affine open. -/
instance IntegralAffineOpen.isIntegral (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : IsIntegral (V.1 : Scheme) := V.2

/-- The affine-open property stored by an integral affine open. -/
instance IntegralAffineOpen.isAffine (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : IsAffine (V.1 : Scheme) := inferInstance

/-- The étale object represented by an integral affine open subscheme. -/
noncomputable def IntegralAffineOpen.toEtale (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : X.left.Etale :=
  Scheme.Etale.mk ((V.1 : U.left.Opens).ι ≫ U.hom)

/-- The inclusion of an integral affine open into its ambient étale object. -/
noncomputable def IntegralAffineOpen.inclusion (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : V.toEtale ⟶ U :=
  MorphismProperty.Over.homMk ((V.1 : U.left.Opens).ι) (by
    dsimp [IntegralAffineOpen.toEtale]
    rfl)

/-- The open subscheme attached to an integral affine open is integral. -/
instance IntegralAffineOpen.toEtale_isIntegral (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : IsIntegral V.toEtale.left := by
  change IsIntegral (V.1 : Scheme)
  exact V.2

/-- The open subscheme attached to an integral affine open is affine. -/
instance IntegralAffineOpen.toEtale_isAffine (U : X.left.Etale)
    (V : IntegralAffineOpen X U) : IsAffine V.toEtale.left := by
  change IsAffine (V.1 : Scheme)
  infer_instance

/-- The integral affine opens cover every étale object. -/
theorem integralAffineOpenCover (U : X.left.Etale) :
    Sieve.ofArrows (fun V : IntegralAffineOpen X U => V.toEtale)
        (fun V => V.inclusion) ∈ X.left.smallEtaleTopology U := sorry

/-- Every étale object over the smooth curve is locally Noetherian. -/
theorem isLocallyNoetherian (U : X.left.Etale) : IsLocallyNoetherian U.left := by
  exact @LocallyOfFiniteType.isLocallyNoetherian U.left X.left U.hom inferInstance
    (LocallyOfFiniteType.isLocallyNoetherian X.hom)

variable (U : X.left.Etale) [IsIntegral U.left]

/-- The image of the generic point of an integral étale object is the generic point. -/
theorem genericPoint_image : U.hom (genericPoint U.left) = genericPoint X.left := sorry

/-- The generic point of an integral étale object lifted to its generic fibre. -/
noncomputable def genericPointLift :
    Spec (U.left.residueField (genericPoint U.left)) ⟶
      (smallEtalePullback (genericPointInclusion X)).obj U |>.left :=
  pullback.lift
    (U.left.fromSpecResidueField (genericPoint U.left))
    (Spec.map ((X.left.residueFieldCongr (genericPoint_image X U)).inv ≫
      U.hom.residueFieldMap (genericPoint U.left)))
    (by sorry)

/-- Evaluation of a generic-fibre unit in the function field of an integral object. -/
noncomputable def genericUnit :
    Γ(((smallEtalePullback (genericPointInclusion X)).obj U).left, ⊤)ˣ →*
      U.left.functionFieldˣ :=
  Units.map
    ((IsLocalRing.ResidueField.lift (RingHom.id U.left.functionField)).comp
      ((Scheme.ΓSpecIso (U.left.residueField (genericPoint U.left))).hom.hom.comp
        (genericPointLift X U).appTop.hom))

/-- The order of a generic-fibre unit at a point of a closed fibre. -/
noncomputable def fibreOrder (x : ClosedPoint X) :
    Additive Γ(((smallEtalePullback (genericPointInclusion X)).obj U).left, ⊤)ˣ →+
      ((smallEtalePullback (closedPointInclusion X x.1 x.2)).obj U).left → ULift.{u} ℤ :=
  AddMonoidHom.mk'
    (fun s point =>
      ULift.up
        (@Scheme.ord U.left inferInstance (isLocallyNoetherian X U)
          (genericUnit X U (Additive.toMul s)).val
          ((pullback.fst U.hom (closedPointInclusion X x.1 x.2)) point)))
    (by sorry)

/-- Fibre orders commute with restriction along a morphism of integral étale objects. -/
theorem fibreOrder_map {V : X.left.Etale} [IsIntegral V.left]
    (f : U ⟶ V) (x : ClosedPoint X) (s :
      Additive Γ(((smallEtalePullback (genericPointInclusion X)).obj V).left, ⊤)ˣ)
    (point : ((smallEtalePullback (closedPointInclusion X x.1 x.2)).obj U).left) :
    fibreOrder X U x ((unitsAddPresheaf _).map
        ((smallEtalePullback (genericPointInclusion X)).map f).op s) point =
      fibreOrder X V x s (((smallEtalePullback (closedPointInclusion X x.1 x.2)).map f).left
        point) := sorry

/-- On an integral affine étale object, a fibre order has finite support. -/
theorem fibreOrder_finite (hU : IsAffine U.left) (s :
      Additive Γ(((smallEtalePullback (genericPointInclusion X)).obj U).left, ⊤)ˣ) :
    {x : ClosedPoint X | fibreOrder X U x s ≠ 0}.Finite := sorry

end EtaleOrders

end AlgebraicGeometry.SchemeOverField
