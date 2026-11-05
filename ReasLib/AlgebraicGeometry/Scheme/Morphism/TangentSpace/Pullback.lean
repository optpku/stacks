/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Product

/-!
# Tangent spaces of scheme pullbacks

This file constructs the projection and fibre-inclusion maps on tangent spaces at the point of
a scheme pullback selected by compatible residue-field identifications.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry.Scheme.Pullback

/-- Transport a tangent vector across the equality between the two structure morphisms from a
scheme pullback to its base. -/
def pullbackTangentSpaceTransport
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (xy : (pullback f g : Scheme)) :
    tangentSpaceAt (pullback.fst f g ≫ f) xy →
      tangentSpaceAt (pullback.snd f g ≫ g) xy :=
  fun D ↦
    Eq.mp
      (by
        simpa using
          congrArg (fun φ : pullback f g ⟶ S ↦ tangentSpaceAt φ xy)
            (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g))
      D

/-- The morphism of fixed fibres that sends a point of `X` over the common base point to its
pair with the fixed point `y` of `Y`. -/
noncomputable def pullbackFiberInl
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    f.fiber (f x) ⟶ (pullback.fst f g ≫ f).fiber ((pullback.fst f g ≫ f) xy) :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let h := pullback.fst f g ≫ f
  let e := residueFieldEquivOfBaseMapBijective f g x y hxy hx hy
  let ex : S.residueField (f x) ≃+* X.residueField x :=
    RingEquiv.ofBijective (f.residueFieldMap x).hom hx
  let baseToY := ex.trans e
  let toY : f.fiber (f x) ⟶ Y :=
    f.fiberToSpecResidueField (f x) ≫
      Spec.map (CommRingCat.ofHom baseToY.symm.toRingHom) ≫ Y.fromSpecResidueField y
  let toProduct : f.fiber (f x) ⟶ pullback f g :=
    pullback.lift (f.fiberι (f x)) toY (by sorry)
  let hfstxy := pointOfBaseResidueFieldMapBijective_fst f g x y hxy hx hy
  let hb : h xy = f x := congrArg f hfstxy
  pullback.lift toProduct
    (f.fiberToSpecResidueField (f x) ≫ Spec.map (S.residueFieldCongr hb).hom)
    (by sorry)

/-- The morphism of fixed fibres that sends a point of `Y` over the common base point to its
pair with the fixed point `x` of `X`. -/
noncomputable def pullbackFiberInr
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    g.fiber (g y) ⟶ (pullback.fst f g ≫ f).fiber ((pullback.fst f g ≫ f) xy) :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let h := pullback.fst f g ≫ f
  let e := residueFieldEquivOfBaseMapBijective f g x y hxy hx hy
  let ey : S.residueField (g y) ≃+* Y.residueField y :=
    RingEquiv.ofBijective (g.residueFieldMap y).hom hy
  let baseToX := ey.trans e.symm
  let toX : g.fiber (g y) ⟶ X :=
    g.fiberToSpecResidueField (g y) ≫
      Spec.map (CommRingCat.ofHom baseToX.symm.toRingHom) ≫ X.fromSpecResidueField x
  let toProduct : g.fiber (g y) ⟶ pullback f g :=
    pullback.lift toX (g.fiberι (g y)) (by sorry)
  let hfstxy := pointOfBaseResidueFieldMapBijective_fst f g x y hxy hx hy
  let hb : h xy = g y := (congrArg f hfstxy).trans hxy
  pullback.lift toProduct
    (g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr hb).hom)
    (by sorry)

/-- The first fixed-fibre inclusion sends the distinguished point over `x` to the distinguished
point of the pullback over the selected pair. -/
theorem pullbackFiberInl_asFiber
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    pullbackFiberInl f g x y hxy hx hy (f.asFiber x) =
      (pullback.fst f g ≫ f).asFiber xy := sorry

/-- The second fixed-fibre inclusion sends the distinguished point over `y` to the distinguished
point of the pullback over the selected pair. -/
theorem pullbackFiberInr_asFiber
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    pullbackFiberInr f g x y hxy hx hy (g.asFiber y) =
      (pullback.fst f g ≫ f).asFiber xy := sorry

/-- The first fixed-fibre inclusion induces a bijection on residue fields at its distinguished
point. -/
theorem pullbackFiberInl_residueFieldMap_bijective
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    Function.Bijective
      ((pullbackFiberInl f g x y hxy hx hy).residueFieldMap (f.asFiber x)).hom := sorry

/-- The second fixed-fibre inclusion induces a bijection on residue fields at its distinguished
point. -/
theorem pullbackFiberInr_residueFieldMap_bijective
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    Function.Bijective
      ((pullbackFiberInr f g x y hxy hx hy).residueFieldMap (g.asFiber y)).hom := sorry

/-- The pair of tangent maps induced by the two projections from a scheme pullback. -/
noncomputable def pullbackTangentProjection
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    -- Local instance justification (noncanonical choice): transport the right tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    tangentSpaceAt (pullback.fst f g ≫ f) xy →ₗ[X.residueField x]
      tangentSpaceAt f x × tangentSpaceAt g y :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let hfstxy := pointOfBaseResidueFieldMapBijective_fst f g x y hxy hx hy
  let hsndxy := pointOfBaseResidueFieldMapBijective_snd f g x y hxy hx hy
  let hfst := fst_residueFieldMap_bijective_of_base f g x y hx hy xy hfstxy hsndxy
  let hsnd := snd_residueFieldMap_bijective_of_base f g x y hx hy xy hfstxy hsndxy
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- first-projection residue-field map.
  let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
    Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- equivalence between the two point residue fields.
  let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
    Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
  { toFun := fun D ↦
      Eq.mp
        (congrArg₂ (fun a b ↦ tangentSpaceAt f a × tangentSpaceAt g b) hfstxy hsndxy)
        (relativeTangentMapAt (pullback.fst f g) f xy hfst D,
          relativeTangentMapAt (pullback.snd f g) g xy hsnd
            (pullbackTangentSpaceTransport f g xy D))
    map_add' := sorry
    map_smul' := sorry }

/-- Evaluating the projection map gives the pair of maps on tangent spaces induced by the two
pullback projections. -/
theorem pullbackTangentProjection_apply
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom)
    (D : tangentSpaceAt (pullback.fst f g ≫ f)
      (pointOfBaseResidueFieldMapBijective f g x y hxy hx hy)) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    let hfstxy := pointOfBaseResidueFieldMapBijective_fst f g x y hxy hx hy
    let hsndxy := pointOfBaseResidueFieldMapBijective_snd f g x y hxy hx hy
    let hfst := fst_residueFieldMap_bijective_of_base f g x y hx hy xy hfstxy hsndxy
    let hsnd := snd_residueFieldMap_bijective_of_base f g x y hx hy xy hfstxy hsndxy
    pullbackTangentProjection f g x y hxy hx hy D =
      Eq.mp
        (congrArg₂ (fun a b ↦ tangentSpaceAt f a × tangentSpaceAt g b) hfstxy hsndxy)
        (relativeTangentMapAt (pullback.fst f g) f xy hfst D,
          relativeTangentMapAt (pullback.snd f g) g xy hsnd
            (pullbackTangentSpaceTransport f g xy D)) := sorry

/-- The tangent map induced by pairing a varying point of the first fibre with the fixed point
`y`, transported through the canonical tangent-space identifications with fibres. -/
noncomputable def pullbackTangentInl
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the target tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    tangentSpaceAt f x →ₗ[X.residueField x]
      tangentSpaceAt (pullback.fst f g ≫ f) xy :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let h := pullback.fst f g ≫ f
  let q := pullbackFiberInl f g x y hxy hx hy
  let hq := pullbackFiberInl_asFiber f g x y hxy hx hy
  -- The projection supplies the value-field map in the required direction;
  -- no inverse of the fixed-fibre inclusion's residue-field map is needed.
  let valueMap := (pointFstResidueFieldMap f g x y hxy hx hy).hom
  let stalkMap : (h.fiber (h xy)).presheaf.stalk (h.asFiber xy) ⟶
      (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
    ((h.fiber (h xy)).presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
      q.stalkMap (f.asFiber x)
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- first-projection residue-field map.
  let _ : Module (X.residueField x) (tangentSpaceAt h xy) :=
    Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
  { toFun := fun D ↦
      (relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt h xy).symm
        { toFun := fun a ↦ valueMap
            ((relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt f x D) (stalkMap.hom a))
          map_add' := sorry
          map_smul' := sorry
          map_one_eq_zero' := sorry
          leibniz' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- The tangent map induced by pairing the fixed point `x` with a varying point of the second
fibre, transported through the canonical tangent-space identifications with fibres. -/
noncomputable def pullbackTangentInr
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the source tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    -- Local instance justification (noncanonical choice): restrict the target tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    tangentSpaceAt g y →ₗ[X.residueField x]
      tangentSpaceAt (pullback.fst f g ≫ f) xy :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let h := pullback.fst f g ≫ f
  let q := pullbackFiberInr f g x y hxy hx hy
  let hq := pullbackFiberInr_asFiber f g x y hxy hx hy
  -- Use the second projection directly on values, after identifying its
  -- image point with `y`, rather than inverting the inclusion's residue map.
  let hsndxy := pointOfBaseResidueFieldMapBijective_snd f g x y hxy hx hy
  let valueMap :=
    ((Y.residueFieldCongr hsndxy).inv ≫ (pullback.snd f g).residueFieldMap xy).hom
  let stalkMap : (h.fiber (h xy)).presheaf.stalk (h.asFiber xy) ⟶
      (g.fiber (g y)).presheaf.stalk (g.asFiber y) :=
    ((h.fiber (h xy)).presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
      q.stalkMap (g.asFiber y)
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- equivalence between the point residue fields.
  let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
    Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- first-projection residue-field map.
  let _ : Module (X.residueField x) (tangentSpaceAt h xy) :=
    Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
  { toFun := fun D ↦
      (relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt h xy).symm
        { toFun := fun a ↦ valueMap
            ((relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt g y D) (stalkMap.hom a))
          map_add' := sorry
          map_smul' := sorry
          map_one_eq_zero' := sorry
          leibniz' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- The linear map from the direct sum of the two factor tangent spaces obtained by adding the
two tangent maps induced by the fixed-fibre inclusions. -/
noncomputable def pullbackTangentCopairing
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the right tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    tangentSpaceAt f x × tangentSpaceAt g y →ₗ[X.residueField x]
      tangentSpaceAt (pullback.fst f g ≫ f) xy :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- equivalence between the point residue fields.
  let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
    Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- first-projection residue-field map.
  let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
    Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
  LinearMap.coprod
    (pullbackTangentInl f g x y hxy hx hy)
    (pullbackTangentInr f g x y hxy hx hy)

/-- The relative tangent space of a scheme pullback at the point selected by two residue-field
identifications is the direct sum of the relative tangent spaces of the two factors. Its forward
map is induced by the projections and its inverse by the two fixed-fibre inclusions. -/
noncomputable def pullbackTangentEquiv
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    -- Local instance justification (noncanonical choice): transport the right tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    tangentSpaceAt (pullback.fst f g ≫ f) xy ≃ₗ[X.residueField x]
      tangentSpaceAt f x × tangentSpaceAt g y :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- first-projection residue-field map.
  let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
    Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
  -- Local instance justification (noncanonical choice): restrict scalars along the selected
  -- equivalence between the point residue fields.
  let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
    Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
  { toLinearMap := pullbackTangentProjection f g x y hxy hx hy
    invFun := pullbackTangentCopairing f g x y hxy hx hy
    left_inv := sorry
    right_inv := sorry }

/-- The forward linear map of the pullback tangent-space equivalence is the pair of tangent maps
induced by the two projections. -/
theorem pullbackTangentEquiv_toLinearMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    -- Local instance justification (noncanonical choice): transport the right tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    (pullbackTangentEquiv f g x y hxy hx hy).toLinearMap =
      pullbackTangentProjection f g x y hxy hx hy := sorry

/-- The inverse linear map of the pullback tangent-space equivalence is the sum of the tangent
maps induced by the two fixed-fibre inclusions. -/
theorem pullbackTangentEquiv_symm_toLinearMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
    -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
    -- action along the explicitly supplied residue-field identifications.
    let _ : Module (X.residueField x) (tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
      Module.compHom _ (pointFstResidueFieldMap f g x y hxy hx hy).hom
    -- Local instance justification (noncanonical choice): transport the right tangent-space
    -- action through the explicitly supplied residue-field equivalence.
    let _ : Module (X.residueField x) (tangentSpaceAt g y) :=
      Module.compHom _ (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).toRingHom
    (pullbackTangentEquiv f g x y hxy hx hy).symm.toLinearMap =
      pullbackTangentCopairing f g x y hxy hx hy := sorry

end AlgebraicGeometry.Scheme.Hom
