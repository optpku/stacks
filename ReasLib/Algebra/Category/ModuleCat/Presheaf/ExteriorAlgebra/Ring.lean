/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring-valued exterior-algebra presheaves

This file retains the multiplicative structure of the sectionwise exterior algebra and relates
its underlying additive presheaf to the existing module-presheaf construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ CommRingCat.{w})
variable (F : PresheafOfModules.{w} (RingPresheaf R))

/-- The exterior algebra of a module of sections, retaining its ring structure. -/
abbrev ringObj (U : Cᵒᵖ) : RingCat.{w} :=
  RingCat.of (ExteriorAlgebra (R.obj U) (sectionObj R F U))

/-- The multiplicative restriction map between sectionwise exterior algebras. -/
noncomputable abbrev ringMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    ringObj R F U ⟶ ringObj R F V :=
  RingCat.ofHom (ModuleCat.exteriorAlgebra.mapRestrictScalarsRingHom
    (R.map i).hom (restriction R F i))

/-- The ring-valued exterior-algebra restriction maps preserve identities. -/
theorem ringMap_id (U : Cᵒᵖ) :
    ringMap R F (𝟙 U) = 𝟙 (ringObj R F U) := sorry

/-- The ring-valued exterior-algebra restriction maps preserve composition. -/
theorem ringMap_comp {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    ringMap R F (i ≫ j) = ringMap R F i ≫ ringMap R F j := sorry

/-- The ring-valued sectionwise exterior-algebra presheaf. -/
@[stacks 01CH "ring-valued exterior-algebra presheaf"]
noncomputable def ringPresheaf : Cᵒᵖ ⥤ RingCat.{w} where
  obj := ringObj R F
  map := ringMap R F
  map_id := ringMap_id R F
  map_comp := ringMap_comp R F

/-- The objectwise structural ring map into the sectionwise exterior algebra. -/
noncomputable abbrev ringUnitApp (U : Cᵒᵖ) :
    (RingPresheaf R).obj U ⟶ ringObj R F U :=
  RingCat.ofHom
    (algebraMap (R.obj U) (ExteriorAlgebra (R.obj U) (sectionObj R F U)))

/-- The structural maps into exterior algebras commute with restriction. -/
theorem ringUnit_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    (RingPresheaf R).map i ≫ ringUnitApp R F V =
      ringUnitApp R F U ≫ (ringPresheaf R F).map i := sorry

/-- The canonical structural map from the base ring presheaf to the exterior-algebra presheaf. -/
@[stacks 01CH "exterior-algebra presheaf structure map"]
noncomputable def ringUnit : RingPresheaf R ⟶ ringPresheaf R F where
  app := ringUnitApp R F
  naturality := fun {_ _} i ↦ ringUnit_naturality R F i

/-- Naturality of the forward identity comparison between the two additive exterior-algebra
presheaves. -/
@[stacks 01CH "forward additive exterior-algebra comparison naturality"]
theorem addCommGrpPresheafNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat).map i) ≫ 𝟙 _ =
      𝟙 _ ≫ (presheaf R F).presheaf.map i := sorry

/-- Naturality of the inverse identity comparison between the two additive exterior-algebra
presheaves. -/
@[stacks 01CH "inverse additive exterior-algebra comparison naturality"]
theorem addCommGrpPresheafInvNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((presheaf R F).presheaf.map i) ≫ 𝟙 _ =
      𝟙 _ ≫ (ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat).map i := sorry

/-- The forward natural transformation forgetting multiplication from the ring-valued
exterior-algebra presheaf. -/
@[stacks 01CH "forward additive exterior-algebra comparison natural transformation"]
noncomputable def addCommGrpPresheafNatTrans :
    ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat ⟶
      (presheaf R F).presheaf where
  app U := 𝟙 _
  naturality _ _ i := addCommGrpPresheafNatTrans_naturality R F i

/-- The inverse natural transformation restoring the ring-valued exterior-algebra presheaf
from its underlying additive presheaf. -/
@[stacks 01CH "inverse additive exterior-algebra comparison natural transformation"]
noncomputable def addCommGrpPresheafInvNatTrans :
    (presheaf R F).presheaf ⟶
      ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat where
  app U := 𝟙 _
  naturality _ _ i := addCommGrpPresheafInvNatTrans_naturality R F i

/-- The forward and inverse additive exterior-algebra comparison transformations compose to
the identity. -/
@[simp, stacks 01CH "additive exterior-algebra comparison forward-inverse law"]
theorem addCommGrpPresheafNatTrans_hom_inv_id :
    addCommGrpPresheafNatTrans R F ≫ addCommGrpPresheafInvNatTrans R F = 𝟙 _ := sorry

/-- The inverse and forward additive exterior-algebra comparison transformations compose to
the identity. -/
@[simp, stacks 01CH "additive exterior-algebra comparison inverse-forward law"]
theorem addCommGrpPresheafNatTrans_inv_hom_id :
    addCommGrpPresheafInvNatTrans R F ≫ addCommGrpPresheafNatTrans R F = 𝟙 _ := sorry

/-- Forgetting multiplication from the ring-valued exterior-algebra presheaf recovers the
additive presheaf underlying the module-valued exterior algebra. -/
@[stacks 01CH "exterior-algebra additive comparison natural isomorphism"]
noncomputable def addCommGrpPresheafIso :
    ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat ≅
      (presheaf R F).presheaf where
  hom := addCommGrpPresheafNatTrans R F
  inv := addCommGrpPresheafInvNatTrans R F
  hom_inv_id := addCommGrpPresheafNatTrans_hom_inv_id R F
  inv_hom_id := addCommGrpPresheafNatTrans_inv_hom_id R F

/-- The forward natural transformation of `addCommGrpPresheafIso`. -/
@[simp, stacks 01CH "exterior-algebra additive comparison isomorphism hom"]
theorem addCommGrpPresheafIso_hom :
    (addCommGrpPresheafIso R F).hom = addCommGrpPresheafNatTrans R F := sorry

/-- The inverse natural transformation of `addCommGrpPresheafIso`. -/
@[simp, stacks 01CH "exterior-algebra additive comparison isomorphism inverse"]
theorem addCommGrpPresheafIso_inv :
    (addCommGrpPresheafIso R F).inv = addCommGrpPresheafInvNatTrans R F := sorry

/-- A component of `addCommGrpPresheafIso` is the objectwise identity comparison. -/
@[simp, stacks 01CH "exterior-algebra additive comparison isomorphism component"]
theorem addCommGrpPresheafIso_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).app U = Iso.refl ((presheaf R F).presheaf.obj U) := sorry

/-- The forward component of `addCommGrpPresheafIso` is the identity morphism. -/
@[simp, stacks 01CH "exterior-algebra additive comparison isomorphism hom component"]
theorem addCommGrpPresheafIso_hom_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).hom.app U = 𝟙 ((presheaf R F).presheaf.obj U) := sorry

/-- The inverse component of `addCommGrpPresheafIso` is the identity morphism. -/
@[simp, stacks 01CH "exterior-algebra additive comparison isomorphism inverse component"]
theorem addCommGrpPresheafIso_inv_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).inv.app U = 𝟙 ((presheaf R F).presheaf.obj U) := sorry

end PresheafOfModules.ExteriorAlgebra
