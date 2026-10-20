/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Forward

/-!
# Construction of the explicit categorical-pullback reindexing comparison

For a specified cleavage on the right leg, this module constructs the
objectwise comparison between pullback-fiber reindexing followed by right
strictification and the opposite order. It owns the concrete cartesian
composites, ambient comparison, and objectwise fiber isomorphism. Naturality,
conjugation, and coherence are layered above this construction.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback.Reindex.explicit

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The common base arrow of the two cartesian composites used to compare pullback-fiber
reindexing with right-leg reindexing. -/
noncomputable def comparisonBaseMap
    (u : C ⥤ D) (p : S ⥤ D) {U V : C} (a : V ⟶ U)
    (X : (π₁ u p).Fiber U) :
    u.obj V ⟶ p.obj X.1.snd :=
  u.map a ≫ (Fiber.forward.iso u p X).hom

/-- First reindex in the induced pullback cleavage and then strictify the right component. -/
noncomputable def comparisonSource
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.Fiber (u.obj V) :=
  Fiber.forward.strict u p χ
    ((χ.ofRight u).reindexObj a X)

/-- First strictify the right component and then reindex it along the image base arrow. -/
noncomputable def comparisonTarget
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.Fiber (u.obj V) :=
  χ.reindexObj (u.map a) (Fiber.forward.strict u p χ X)

/-- The cartesian composite from the source presentation of the reindexing comparison to the
original right component. -/
noncomputable def comparisonSourceCartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonSource u p χ a X).1 ⟶ X.1.snd :=
  Fiber.forward.cartesian u p χ
      ((χ.ofRight u).reindexObj a X) ≫
    ((χ.ofRight u).cartesianHom a X).snd

/-- The cartesian composite from the target presentation of the reindexing comparison to the
original right component. -/
noncomputable def comparisonTargetCartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonTarget u p χ a X).1 ⟶ X.1.snd :=
  χ.cartesianHom (u.map a) (Fiber.forward.strict u p χ X) ≫
    Fiber.forward.cartesian u p χ X

/-- The source cartesian composite lies over the displayed common base arrow and is strongly
cartesian. -/
instance comparisonSourceCartesian.isStronglyCartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.IsStronglyCartesian (comparisonBaseMap u p a X)
      (comparisonSourceCartesian u p χ a X) := sorry

/-- The target cartesian composite lies over the displayed common base arrow and is strongly
cartesian. -/
instance comparisonTargetCartesian.isStronglyCartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.IsStronglyCartesian (comparisonBaseMap u p a X)
      (comparisonTargetCartesian u p χ a X) := sorry

/-- The ambient-domain comparison between the two cartesian composites defining reindexing
compatibility. -/
noncomputable def comparisonAmbientIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonSource u p χ a X).1 ≅ (comparisonTarget u p χ a X).1 :=
  IsStronglyCartesian.domainIsoOfBaseIso
    (R := u.obj V) (R' := u.obj V) (S := p.obj X.1.snd)
    (a := (comparisonTarget u p χ a X).1)
    (a' := (comparisonSource u p χ a X).1)
    (b := X.1.snd)
    (f := comparisonBaseMap u p a X)
    (f' := comparisonBaseMap u p a X)
    (g := Iso.refl (u.obj V)) p
    (Category.id_comp _).symm
    (comparisonTargetCartesian u p χ a X)
    (comparisonSourceCartesian u p χ a X)

/-- The forward ambient comparison lies over the identity of `u.obj V`. -/
theorem comparisonAmbientIso.hom.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.IsHomLift (𝟙 (u.obj V))
      (comparisonAmbientIso u p χ a X).hom := sorry

/-- The inverse ambient comparison lies over the identity of `u.obj V`. -/
theorem comparisonAmbientIso.inv.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    p.IsHomLift (𝟙 (u.obj V))
      (comparisonAmbientIso u p χ a X).inv := sorry

/-- The forward morphism in the right fiber comparing the two orders of strictification and
reindexing. -/
noncomputable def comparisonHom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    comparisonSource u p χ a X ⟶ comparisonTarget u p χ a X :=
  ⟨(comparisonAmbientIso u p χ a X).hom,
    comparisonAmbientIso.hom.isHomLift u p χ a X⟩

/-- The inverse morphism in the right fiber comparing the two orders of strictification and
reindexing. -/
noncomputable def comparisonInv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    comparisonTarget u p χ a X ⟶ comparisonSource u p χ a X :=
  ⟨(comparisonAmbientIso u p χ a X).inv,
    comparisonAmbientIso.inv.isHomLift u p χ a X⟩

/-- The forward and inverse fiber comparisons compose to the identity on the source object. -/
theorem comparisonHom.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    comparisonHom u p χ a X ≫ comparisonInv u p χ a X =
      𝟙 (comparisonSource u p χ a X) := sorry

/-- The inverse and forward fiber comparisons compose to the identity on the target object. -/
theorem comparisonInv.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    comparisonInv u p χ a X ≫ comparisonHom u p χ a X =
      𝟙 (comparisonTarget u p χ a X) := sorry

/-- The objectwise comparison between pullback-fiber reindexing followed by right-component
strictification and right-component strictification followed by right-leg reindexing. -/
noncomputable def comparisonIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    comparisonSource u p χ a X ≅ comparisonTarget u p χ a X where
  hom := comparisonHom u p χ a X
  inv := comparisonInv u p χ a X
  hom_inv_id := comparisonHom.inv u p χ a X
  inv_hom_id := comparisonInv.hom u p χ a X

/-- The forward morphism of the objectwise comparison is the cartesianly characterized
comparison morphism. -/
@[simp]
theorem comparisonIso.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonIso u p χ a X).hom = comparisonHom u p χ a X := sorry

/-- The inverse morphism of the objectwise comparison is the inverse cartesianly characterized
comparison morphism. -/
@[simp]
theorem comparisonIso.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonIso u p χ a X).inv = comparisonInv u p χ a X := sorry

/-- The forward reindexing comparison is characterized by its composite with the target
cartesian composite. -/
@[reassoc]
theorem comparisonIso.hom.fac
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonIso u p χ a X).hom.1 ≫ comparisonTargetCartesian u p χ a X =
      comparisonSourceCartesian u p χ a X := sorry

/-- The inverse reindexing comparison is characterized by its composite with the source
cartesian composite. -/
@[reassoc]
theorem comparisonIso.inv.fac
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonIso u p χ a X).inv.1 ≫ comparisonSourceCartesian u p χ a X =
      comparisonTargetCartesian u p χ a X := sorry

end Limits.CategoricalPullback.Reindex.explicit

end CategoryTheory
