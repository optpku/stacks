/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# The ringed topos inherited along a fibred projection

For a fibred projection `p : S ⥤ X`, this leaf equips the inherited topology on `S` with the
actual ring-valued inverse image of `X.structureSheaf`.  The resulting projection is an arbitrary
`RingedSite.ToposHom`; it does not impose the representable-flatness needed by the stronger
ringed-site presentation in `RingedSite.Fibered.Inherited`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Functor

variable {X : RingedSite.{u, v, max u v}} {S : Type u} [Category.{v} S]

/-- The site-presented ringed topos on the topology inherited along a fibred projection `p`.
Its structure sheaf is definitionally the ring-valued inverse image of `X.structureSheaf`. -/
@[stacks 08P8 "inherited ringed topos"]
noncomputable abbrev inheritedRingedTopos (p : S ⥤ X.carrier) [p.IsFibered] :
    RingedSite.{u, v, max u v} :=
  RingedSite.ofRingSheaf (p.inheritedTopology X.siteTopology)
    (((inheritedTopology.morphismOfTopoi p X.siteTopology).ringInverseImage).obj
      X.structureSheaf)

/-- The topology underlying `p.inheritedRingedTopos` is the topology inherited along `p`. -/
@[simp, stacks 08P8 "inherited ringed-topos topology"]
theorem inheritedRingedTopos_siteTopology (p : S ⥤ X.carrier) [p.IsFibered] :
    p.inheritedRingedTopos.siteTopology = p.inheritedTopology X.siteTopology := sorry

/-- The structure sheaf of `p.inheritedRingedTopos` is the ring-valued inverse image of the
structure sheaf on `X`. -/
@[simp, stacks 08P8 "inherited ringed-topos structure sheaf"]
theorem inheritedRingedTopos_structureSheaf (p : S ⥤ X.carrier) [p.IsFibered] :
    p.inheritedRingedTopos.structureSheaf =
      ((inheritedTopology.morphismOfTopoi p X.siteTopology).ringInverseImage).obj
        X.structureSheaf := sorry

/-- The canonical morphism from the ringed topos inherited along a
fibred projection to its base ringed topos. -/
@[stacks 08P8 "inherited projection morphism of ringed topoi"]
noncomputable def inheritedProjectionToposHom (p : S ⥤ X.carrier) [p.IsFibered] :
    RingedSite.ToposHom p.inheritedRingedTopos X where
  toTopos := inheritedTopology.morphismOfTopoi p X.siteTopology
  structureMap :=
    𝟙 (((inheritedTopology.morphismOfTopoi p X.siteTopology).ringInverseImage).obj
      X.structureSheaf)

/-- The underlying topos morphism of `p.inheritedProjectionToposHom` is the canonical morphism
induced by the fibred projection. -/
@[simp, stacks 08P8 "underlying inherited projection morphism"]
theorem inheritedProjectionToposHom_toTopos (p : S ⥤ X.carrier) [p.IsFibered] :
    p.inheritedProjectionToposHom.toTopos =
      inheritedTopology.morphismOfTopoi p X.siteTopology := sorry

/-- The structure map of `p.inheritedProjectionToposHom` is the identity of the inherited
ring-valued inverse image. -/
@[simp, stacks 08P8 "inherited projection structure map"]
theorem inheritedProjectionToposHom_structureMap (p : S ⥤ X.carrier) [p.IsFibered] :
    p.inheritedProjectionToposHom.structureMap =
      𝟙 (((inheritedTopology.morphismOfTopoi p X.siteTopology).ringInverseImage).obj
        X.structureSheaf) := sorry

-- The two public data owners are assembled from the canonical inherited-topology morphism and
-- its ring-valued inverse image; their non-Prop fields are not supplied by `sorry`.

end CategoryTheory.Functor

namespace CategoryTheory.CartesianBasedFunctor

variable {X : RingedSite.{u, v, max u v}} {S₁ S₂ : Type u}
variable [Category.{v} S₁] [Category.{v} S₂]
variable {p₁ : S₁ ⥤ X.carrier} {p₂ : S₂ ⥤ X.carrier}
variable (F : CartesianBasedFunctor p₁ p₂)
variable [p₁.IsFibered] [p₂.IsFibered]

namespace inheritedToposHom

/-- The direct-image comparison identifying the composite of an inherited-topology morphism
and the target projection with the source projection. -/
@[stacks 08PA "inherited projection direct-image comparison"]
noncomputable def projectionPushforwardIso :
    (MorphismOfTopoiIn.comp
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology)).pushforward ≅
      (Functor.inheritedTopology.morphismOfTopoi p₁ X.siteTopology).pushforward :=
  Functor.sheafPushforwardCocontinuousComp'
    (uv := p₁) (p₁.inheritedTopology X.siteTopology)
    (p₂.inheritedTopology X.siteTopology) X.siteTopology F.toFunctor p₂
    (eqToIso (F.toBasedFunctor.w : F.toFunctor ⋙ p₂ = p₁))

/-- The inverse-image mate of `projectionPushforwardIso`. -/
@[stacks 08PA "inherited projection inverse-image comparison"]
noncomputable def projectionInverseImageIso :
    (MorphismOfTopoiIn.comp
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology)).inverseImage ≅
      (Functor.inheritedTopology.morphismOfTopoi p₁ X.siteTopology).inverseImage :=
  Adjunction.leftAdjointUniq
    ((MorphismOfTopoiIn.comp
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology)).adjunction.ofNatIsoRight
        (projectionPushforwardIso F))
    (Functor.inheritedTopology.morphismOfTopoi p₁ X.siteTopology).adjunction

/-- The ring-valued lift of the inherited projection inverse-image comparison. -/
@[stacks 08PA "ring-valued inherited projection comparison"]
noncomputable def projectionRingInverseImageIso :
    (MorphismOfTopoiIn.comp
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology)).ringInverseImage ≅
      (Functor.inheritedTopology.morphismOfTopoi p₁ X.siteTopology).ringInverseImage :=
  MorphismOfTopoiIn.ringInverseImageNatIso
    (f := MorphismOfTopoiIn.comp
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology))
    (g := Functor.inheritedTopology.morphismOfTopoi p₁ X.siteTopology)
    (projectionInverseImageIso F)

/-- The canonical identification `g⁻¹ 𝒪_C ≅ 𝒪_C'` induced by a cartesian functor
between fibred categories over the same ringed site. -/
@[stacks 08PA "inherited structure-sheaf isomorphism"]
noncomputable def structureSheafIso :
    (F.morphismOfTopoiIn X.siteTopology).ringInverseImage.obj
      p₂.inheritedRingedTopos.structureSheaf ≅
      p₁.inheritedRingedTopos.structureSheaf :=
  ((MorphismOfTopoiIn.ringInverseImageCompIso
      (Functor.inheritedTopology.morphismOfTopoi p₂ X.siteTopology)
      (F.morphismOfTopoiIn X.siteTopology)).symm.app X.structureSheaf) ≪≫
    (projectionRingInverseImageIso F).app X.structureSheaf

end inheritedToposHom

/-- A cartesian functor between fibred categories over a ringed site
induces a morphism between their inherited ringed topoi. -/
@[stacks 08PA "inherited morphism of ringed topoi"]
noncomputable def inheritedToposHom :
    RingedSite.ToposHom p₁.inheritedRingedTopos p₂.inheritedRingedTopos where
  toTopos := F.morphismOfTopoiIn X.siteTopology
  structureMap := (inheritedToposHom.structureSheafIso F).hom

namespace inheritedToposHom

/-- The underlying morphism of topoi of `F.inheritedToposHom` is the one induced by the
cartesian functor on inherited topologies. -/
@[simp, stacks 08PA "underlying inherited topos morphism"]
theorem toTopos :
    F.inheritedToposHom.toTopos = F.morphismOfTopoiIn X.siteTopology := sorry

/-- The structure map of `F.inheritedToposHom` is the forward map of
`structureSheafIso F`. -/
@[simp, stacks 08PA "inherited topos structure map"]
theorem structureMap :
    F.inheritedToposHom.structureMap = (structureSheafIso F).hom := sorry

/-- Compatibility of the inherited projection comparison with the direct-image structure
maps. -/
@[stacks 08PA "inherited projection triangle compatibility"]
theorem projectionTriangle_comm :
    (RingedSite.ToposHom.comp
        F.inheritedToposHom p₂.inheritedProjectionToposHom).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans
        (projectionPushforwardIso F).hom).app p₁.inheritedRingedTopos.structureSheaf =
      p₁.inheritedProjectionToposHom.directStructureMap := sorry

/-- The inherited ringed-topos morphism followed by the target projection is canonically
`2`-isomorphic to the source projection. -/
@[stacks 08PA "commutative triangle of inherited ringed topoi"]
noncomputable def projectionTriangle :
    RingedSite.ToposHom.TwoIso
      (X := p₁.inheritedRingedTopos) (Y := X)
      (RingedSite.ToposHom.comp
        (X := p₁.inheritedRingedTopos)
        (Y := p₂.inheritedRingedTopos) (Z := X)
        F.inheritedToposHom p₂.inheritedProjectionToposHom)
      p₁.inheritedProjectionToposHom where
  homIso := projectionPushforwardIso F
  comm := projectionTriangle_comm F

-- The structure-sheaf isomorphism and ringed-topos morphism are assembled from explicit
-- inverse-image and composition isomorphisms.  The triangle's only deferred field is its
-- Prop-valued compatibility equation.

end inheritedToposHom

end CategoryTheory.CartesianBasedFunctor
