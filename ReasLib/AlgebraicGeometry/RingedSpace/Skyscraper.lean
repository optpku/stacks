module

public import Mathlib.Topology.Sheaves.PUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Topology.Sheaf.Skyscraper

/-!
# Point ringed spaces

This module constructs the one-point ringed space associated to a point of a ringed space and its
canonical map to the ambient space.  It also records the associated stalk-ring identifications.
These constructions are independent of sheaves of modules; the module-valued skyscraper functor
lives in `AlgebraicGeometry.RingedSpace.Module.Skyscraper`.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}

open CategoryTheory.Limits

/-- The presheaf morphism from `X.presheaf` to the direct image of the stalk ring
`X.presheaf.stalk x` on the one-point space; it is the structure-sheaf map underlying
`pointInclusion x`. -/
public noncomputable def pointInclusionPresheafMap (x : X) :
    X.presheaf ⟶
      (ofHom (ContinuousMap.const (TopCat.of PUnit) x)) _*
        (TopCat.Sheaf.Skyscraper.atPoint PUnit.unit (X.presheaf.stalk x)).obj :=
  ((TopCat.Sheaf.Skyscraper.stalkAdjunction x).unit.app X.sheaf).hom ≫
    eqToHom
      (@skyscraperPresheaf_eq_pushforward _ x (fun _ ↦ Classical.dec _) CommRingCat _ _
        (X.presheaf.stalk x) (fun _ ↦ Classical.dec _))

/-- The one-point ringed space `pointRingedSpace x`, modeled on `TopCat.of PUnit` with structure
sheaf the skyscraper sheaf at its unique point valued in `X.presheaf.stalk x`. -/
noncomputable def pointRingedSpace (x : X) : RingedSpace :=
  let pointSheaf := TopCat.Sheaf.Skyscraper.atPoint PUnit.unit (X.presheaf.stalk x)
  { carrier := TopCat.of PUnit
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

/-- The carrier of `pointRingedSpace x` is the one-point space, hence has the indiscrete
topology. -/
instance pointRingedSpace_indiscreteTopology (x : X) :
    IndiscreteTopology (pointRingedSpace x) := sorry

/-- The unique stalk of `pointRingedSpace x` is canonically isomorphic to
`X.presheaf.stalk x`. -/
public noncomputable def PointRingedSpace.stalkIso (x : X) :
    (pointRingedSpace x).presheaf.stalk PUnit.unit ≅ X.presheaf.stalk x :=
  TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes (X := TopCat.of PUnit) PUnit.unit
    (X.presheaf.stalk x)
    (specializes_rfl : PUnit.unit ⤳ PUnit.unit)

/-- The canonical morphism of ringed spaces
`pointInclusion x : pointRingedSpace x ⟶ X`. -/
noncomputable def pointInclusion (x : X) : pointRingedSpace x ⟶ X :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
      c := pointInclusionPresheafMap x }

/-- Unfolding `pointInclusion` identifies its underlying morphism of presheafed spaces. -/
theorem pointInclusion_def (x : X) :
    (pointInclusion x).hom =
      { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
        c := pointInclusionPresheafMap x } := sorry

/-- The underlying continuous map of `pointInclusion x` is the constant map to `x`. -/
@[simp] theorem pointInclusion_hom_base (x : X) :
    (pointInclusion x).hom.base = ofHom (ContinuousMap.const (TopCat.of PUnit) x) := sorry

/-- Evaluating `pointInclusion x` at the unique point of `pointRingedSpace x` returns `x`. -/
@[simp] theorem pointInclusion_hom_base_apply (x : X) :
    (pointInclusion x).hom.base PUnit.unit = x := sorry

/-- The inverse image along `pointInclusion x` of an open containing `x` is the top open of
the one-point ringed space. -/
public theorem RingedSpace.pointInclusion_preimageOpen_eq_top (x : X)
    {U : Opens X} (hxU : x ∈ U) :
    RingedSpace.preimageOpen (pointInclusion x) U = ⊤ := sorry

/-- The inverse image along `pointInclusion x` of an open missing `x` is the bottom open of
the one-point ringed space. -/
public theorem RingedSpace.pointInclusion_preimageOpen_eq_bot (x : X)
    {U : Opens X} (hxU : x ∉ U) :
    RingedSpace.preimageOpen (pointInclusion x) U = ⊥ := sorry

/-- An open subset of the one-point space which contains its unique point is the top open. -/
public theorem pointOpen_eq_top {U : Opens (TopCat.of PUnit)} (h : PUnit.unit ∈ U) :
    U = ⊤ := sorry

/-- After identifying the unique stalk of `pointRingedSpace x` with the stalk of `X` at `x`,
the stalk map induced by `pointInclusion x` is the identity. -/
public theorem RingedSpace.pointInclusion_stalkMap_comp_stalkIso_hom (x : X) :
    ((pointInclusion x).hom.stalkMap PUnit.unit) ≫ (PointRingedSpace.stalkIso x).hom =
      𝟙 (X.presheaf.stalk x) := sorry

/-- The stalk map induced by `pointInclusion x` at the unique point is the inverse of the
canonical stalk identification `PointRingedSpace.stalkIso x`. -/
public theorem RingedSpace.pointInclusion_stalkMap_eq_stalkIso_inv (x : X) :
    ((pointInclusion x).hom.stalkMap PUnit.unit) = (PointRingedSpace.stalkIso x).inv := sorry

/-- The structure sheaf of `pointRingedSpace x`, viewed as a `RingCat`-valued sheaf. -/
public noncomputable abbrev pointRingCatSheaf (x : X) :=
  RingedSpace.ringCatSheaf (pointRingedSpace x)

/-- On the top open of the one-point space, `pointRingCatSheaf x` has value
`RingCat.of (X.presheaf.stalk x)`. -/
theorem pointRingedSpace_ringCatSheaf_obj_top (x : X) :
    (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj.obj (op ⊤) =
      RingCat.of (X.presheaf.stalk x) := sorry

/-- The value of the point-space structure sheaf on its top open is canonically isomorphic to
the stalk ring of `X` at `x`. -/
public noncomputable def PointRingedSpace.ringTopIso (x : X) :
    (pointRingCatSheaf x).obj.obj (op (⊤ : Opens (TopCat.of PUnit))) ≅
      RingCat.of (X.presheaf.stalk x) :=
  eqToIso (pointRingedSpace_ringCatSheaf_obj_top x)

end

end AlgebraicGeometry
