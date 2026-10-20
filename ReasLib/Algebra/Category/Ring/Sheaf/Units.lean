/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Units of a Sheaf of Commutative Rings

This file constructs the sheaf of units of a commutative-ring-valued sheaf on
an arbitrary site, together with its underlying units subsheaf and additive
abelian-sheaf view.  It is independent of module sheaves and of any particular
geometric category.
-/

open CategoryTheory Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace UnitsInternal

/-- The commutative-group-valued presheaf of objectwise units of a commutative ring sheaf. -/
private noncomputable abbrev unitsPresheaf
    (𝒪 : Sheaf J CommRingCat.{w}) :
    Cᵒᵖ ⥤ CommGrpCat.{w} :=
  𝒪.1 ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

/-- The units presheaf of a commutative ring sheaf satisfies the sheaf condition. -/
private theorem unitsPresheaf_isSheaf
    (𝒪 : Sheaf J CommRingCat.{w}) :
    Presheaf.IsSheaf J (unitsPresheaf 𝒪) := sorry

end UnitsInternal

/-- The sheaf `𝒪⁎` of invertible local sections of a commutative-ring-valued sheaf `𝒪`. -/
@[stacks 0409 "(3)"]
public noncomputable def unitsSheaf
    (𝒪 : Sheaf J CommRingCat.{w}) :
    Sheaf J CommGrpCat.{w} :=
  ⟨UnitsInternal.unitsPresheaf 𝒪, UnitsInternal.unitsPresheaf_isSheaf 𝒪⟩

/-- The sections of the units sheaf are the units of the section ring. -/
public theorem unitsSheaf_obj (𝒪 : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ) :
    (unitsSheaf 𝒪).1.obj U = CommGrpCat.of (𝒪.1.obj U)ˣ := sorry

/-- Restriction in the units sheaf is the homomorphism on units induced by ring restriction. -/
public theorem unitsSheaf_map (𝒪 : Sheaf J CommRingCat.{w})
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    HEq ((unitsSheaf 𝒪).1.map f)
      (CommGrpCat.ofHom (Units.map (𝒪.1.map f).hom.toMonoidHom)) := sorry

section UnderlyingTypes

variable [h𝒪 : J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]

namespace UnitsInternal

/-- The underlying type-valued sheaf of a commutative ring sheaf. -/
private noncomputable abbrev underlyingCommRingSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{max u v})).obj 𝒪

/-- Each section of a commutative-ring sheaf has its canonical commutative-ring structure on the underlying section type. -/
-- Local instance justification (defeq pin): `sheafCompose` forgets the bundled commutative-ring structure, so objectwise unit predicates need the canonical structure carried by `𝒪` exposed on the definitionally equal underlying type.
private local instance underlyingCommRingSheaf_commRing
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : Cᵒᵖ) :
    CommRing ((underlyingCommRingSheaf 𝒪).1.obj U) :=
  inferInstanceAs (CommRing (𝒪.1.obj U))

/-- Restriction maps preserve the property of being a unit. -/
private theorem unitsSubfunctor_map
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U V : Cᵒᵖ}
    (f : U ⟶ V) {x : (underlyingCommRingSheaf 𝒪).1.obj U} (hx : IsUnit x) :
    IsUnit ((underlyingCommRingSheaf 𝒪).1.map f x) := sorry

/-- The objectwise units form a subfunctor of the underlying ring-sections presheaf. -/
private noncomputable def unitsSubfunctor
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Subfunctor (underlyingCommRingSheaf 𝒪).1 where
  obj _ := { x | IsUnit x }
  map f := fun _ hx ↦ unitsSubfunctor_map 𝒪 f hx

/-- The objectwise units subfunctor of a commutative ring sheaf is a sheaf. -/
private theorem unitsSubfunctor_isSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Presheaf.IsSheaf J (unitsSubfunctor 𝒪).toFunctor := sorry

/-- The objectwise map from a unit to the corresponding element of the units subfunctor. -/
private noncomputable def unitsToSubfunctorApp
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : Cᵒᵖ) :
      (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}).obj U ⟶
      (unitsSubfunctor 𝒪).toFunctor.obj U :=
  TypeCat.ofHom fun u ↦ ⟨u.1, u.isUnit⟩

/-- The objectwise map from the units subfunctor to the corresponding bundled unit. -/
private noncomputable def unitsFromSubfunctorApp
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : Cᵒᵖ) :
    (unitsSubfunctor 𝒪).toFunctor.obj U ⟶
      (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}).obj U :=
  TypeCat.ofHom fun s ↦ s.2.unit

/-- The objectwise map from units to the units subfunctor is natural. -/
private theorem unitsToSubfunctor_naturality
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U V : Cᵒᵖ} (f : U ⟶ V) :
      (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}).map f ≫
        unitsToSubfunctorApp 𝒪 V =
      unitsToSubfunctorApp 𝒪 U ≫ (unitsSubfunctor 𝒪).toFunctor.map f := sorry

/-- The objectwise map from the units subfunctor to units is natural. -/
private theorem unitsFromSubfunctor_naturality
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (unitsSubfunctor 𝒪).toFunctor.map f ≫ unitsFromSubfunctorApp 𝒪 V =
      unitsFromSubfunctorApp 𝒪 U ≫
        (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}).map f := sorry

/-- The natural transformation from the underlying units presheaf to its units subfunctor. -/
private noncomputable def unitsToSubfunctor
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v} ⟶
      (unitsSubfunctor 𝒪).toFunctor where
  app := unitsToSubfunctorApp 𝒪
  naturality := fun {_ _} f ↦ unitsToSubfunctor_naturality 𝒪 f

/-- The natural transformation from the units subfunctor to the underlying units presheaf. -/
private noncomputable def unitsFromSubfunctor
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (unitsSubfunctor 𝒪).toFunctor ⟶
      unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v} where
  app := unitsFromSubfunctorApp 𝒪
  naturality := fun {_ _} f ↦ unitsFromSubfunctor_naturality 𝒪 f

/-- The map from units to the units subfunctor and its inverse compose to the identity. -/
private theorem unitsToFromSubfunctor_id
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsToSubfunctor 𝒪 ≫ unitsFromSubfunctor 𝒪 =
      𝟙 (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}) := sorry

/-- The map from the units subfunctor to units and its inverse compose to the identity. -/
private theorem unitsFromToSubfunctor_id
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsFromSubfunctor 𝒪 ≫ unitsToSubfunctor 𝒪 =
      𝟙 (unitsSubfunctor 𝒪).toFunctor := sorry

/-- The underlying units presheaf is naturally isomorphic to the units subfunctor. -/
private noncomputable def unitsPresheafForgetIsoSubfunctor
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}) ≅
      (unitsSubfunctor 𝒪).toFunctor where
  hom := unitsToSubfunctor 𝒪
  inv := unitsFromSubfunctor 𝒪
  hom_inv_id := unitsToFromSubfunctor_id 𝒪
  inv_hom_id := unitsFromToSubfunctor_id 𝒪

end UnitsInternal

/-- The underlying type-valued units subsheaf `𝒪⁎ ⊆ 𝒪`. -/
public noncomputable def unitsSubsheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  ⟨(UnitsInternal.unitsSubfunctor 𝒪).toFunctor,
    UnitsInternal.unitsSubfunctor_isSheaf 𝒪⟩

/-- The underlying ring section represented by a section of `𝒪⁎ ⊆ 𝒪`.

This readout keeps downstream constructions independent of the private implementation of the
units subsheaf. -/
@[stacks 0409 "units subsheaf value readout"]
public noncomputable def unitsSubsheafValue
    (𝒪 : Sheaf J CommRingCat.{max u v})
    {U : Cᵒᵖ} (s : (unitsSubsheaf 𝒪).1.obj U) : 𝒪.1.obj U :=
  s.1

namespace UnitsInternal

/-- The morphism from the underlying units sheaf to the units subsheaf. -/
private noncomputable def unitsSheafUnderlyingHom
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (sheafCompose J (CategoryTheory.forget CommGrpCat.{max u v})).obj
        (unitsSheaf 𝒪) ⟶ unitsSubsheaf 𝒪 :=
  ⟨(unitsPresheafForgetIsoSubfunctor 𝒪).hom⟩

/-- The morphism from the units subsheaf to the underlying units sheaf. -/
private noncomputable def unitsSheafUnderlyingInv
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsSubsheaf 𝒪 ⟶
      (sheafCompose J (CategoryTheory.forget CommGrpCat.{max u v})).obj
        (unitsSheaf 𝒪) :=
  ⟨(unitsPresheafForgetIsoSubfunctor 𝒪).inv⟩

/-- The two units-sheaf comparison morphisms compose to the identity on the source. -/
private theorem unitsSheafUnderlying_hom_inv_id
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsSheafUnderlyingHom 𝒪 ≫ unitsSheafUnderlyingInv 𝒪 =
      𝟙 ((sheafCompose J (CategoryTheory.forget CommGrpCat.{max u v})).obj
        (unitsSheaf 𝒪)) := sorry

/-- The two units-sheaf comparison morphisms compose to the identity on the target. -/
private theorem unitsSheafUnderlying_inv_hom_id
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    unitsSheafUnderlyingInv 𝒪 ≫ unitsSheafUnderlyingHom 𝒪 =
      𝟙 (unitsSubsheaf 𝒪) := sorry

end UnitsInternal

/-- The underlying type-valued units sheaf is canonically isomorphic to the units subsheaf
`𝒪⁎ ⊆ 𝒪`. -/
public noncomputable def unitsSheafUnderlyingIso
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (sheafCompose J (CategoryTheory.forget CommGrpCat.{max u v})).obj
        (unitsSheaf 𝒪) ≅ unitsSubsheaf 𝒪 where
  hom := UnitsInternal.unitsSheafUnderlyingHom 𝒪
  inv := UnitsInternal.unitsSheafUnderlyingInv 𝒪
  hom_inv_id := UnitsInternal.unitsSheafUnderlying_hom_inv_id 𝒪
  inv_hom_id := UnitsInternal.unitsSheafUnderlying_inv_hom_id 𝒪

end UnderlyingTypes

namespace UnitsInternal

/-- Forgetting the multiplicative group structure on the units sheaf yields an additive sheaf. -/
private theorem unitsAddPresheaf_isSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Presheaf.IsSheaf J ((unitsSheaf 𝒪).1 ⋙ CommGrpCat.toAddCommGrp) := sorry

end UnitsInternal

/-- The additive commutative-group-valued sheaf attached to the units sheaf `𝒪⁎`, for use in
abelian sheaf cohomology. -/
public noncomputable def unitsAddSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J AddCommGrpCat :=
  ⟨(unitsSheaf 𝒪).1 ⋙ CommGrpCat.toAddCommGrp,
    UnitsInternal.unitsAddPresheaf_isSheaf 𝒪⟩

/-- The underlying ring section represented by a section of the additive units sheaf. -/
@[stacks 0409 "additive units section readout"]
public noncomputable def unitsAddSheafValue
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : Cᵒᵖ}
    (g : (unitsAddSheaf 𝒪).1.obj U) : 𝒪.1.obj U :=
  g.1

end CategoryTheory.Sheaf

namespace SheafOfModules.RingedSite

/- Lean surface notation retained for the ringed-site units API. -/
scoped[RingedSiteUnits] postfix:max "⁎" =>
  _root_.CategoryTheory.Sheaf.unitsSheaf

end SheafOfModules.RingedSite
