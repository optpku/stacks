/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# First exterior powers of module presheaves

The sectionwise maps from a module to its first exterior power assemble into a natural
transformation of dependent module presheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorPower

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Restriction compatibility for the sectionwise first-exterior-power isomorphisms. -/
@[stacks 01CF "sectionwise first exterior power naturality"]
theorem degreeOneIso_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫
        (ModuleCat.restrictScalars ((RingPresheaf O).map f).hom).map
          (ModuleCat.exteriorPower.degreeOneIso (sectionObj O F V)).hom =
      (ModuleCat.exteriorPower.degreeOneIso (sectionObj O F U)).hom ≫
        (presheaf O F 1).map f := sorry

/-- A module presheaf is canonically isomorphic to its first exterior-power presheaf. -/
@[stacks 01CF "module presheaf as its first exterior power"]
noncomputable def degreeOneIso
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    F ≅ presheaf O F 1 :=
  PresheafOfModules.isoMk
    (fun U ↦ ModuleCat.exteriorPower.degreeOneIso (sectionObj O F U))
    (fun _ _ f ↦ degreeOneIso_app_naturality O F f)

/-- The canonical morphism from a module presheaf to its first exterior-power presheaf. -/
@[stacks 01CF "first exterior power module-presheaf map"]
noncomputable def degreeOne
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    F ⟶ presheaf O F 1 :=
  (degreeOneIso O F).hom

/-- The forward component of the presheaf degree-one isomorphism is the module degree-one
isomorphism. -/
@[simp, stacks 01CF "first exterior power isomorphism hom component"]
theorem degreeOneIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (degreeOneIso O F).hom.app U =
      (ModuleCat.exteriorPower.degreeOneIso (sectionObj O F U)).hom := sorry

/-- The inverse component of the presheaf degree-one isomorphism is the inverse module
degree-one isomorphism. -/
@[simp, stacks 01CF "first exterior power isomorphism inverse component"]
theorem degreeOneIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (degreeOneIso O F).inv.app U =
      (ModuleCat.exteriorPower.degreeOneIso (sectionObj O F U)).inv := sorry

/-- Restriction compatibility in terms of the canonical degree-one morphisms. -/
theorem degreeOne_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (ModuleCat.exteriorPower.degreeOne (sectionObj O F V)) =
      ModuleCat.exteriorPower.degreeOne (sectionObj O F U) ≫
        map O F 1 f := sorry

/-- A component of the presheaf degree-one map is the module degree-one map. -/
@[simp, stacks 01CF "first exterior power map component"]
theorem degreeOne_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (degreeOne O F).app U =
      ModuleCat.exteriorPower.degreeOne (sectionObj O F U) := sorry

/-- Degree-one exterior-power maps are natural in the module presheaf. -/
@[stacks 01CF "first exterior power map naturality"]
theorem degreeOne_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    f ≫ degreeOne O G = degreeOne O F ≫ hom O f 1 := sorry

/-- Naturality of the inverse first-exterior-power isomorphisms in a module presheaf. -/
@[stacks 01CF "inverse naturality of the first exterior power"]
theorem degreeOneIso_inv_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    hom O f 1 ≫ (degreeOneIso O G).inv =
      (degreeOneIso O F).inv ≫ f := sorry

/-- The degree-one maps form the forward natural transformation from the identity functor. -/
@[stacks 01CF "forward first exterior power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf O) ⥤
      PresheafOfModules.{w} (RingPresheaf O)) ⟶ functor O 1 where
  app F := degreeOne O F
  naturality _ _ f := degreeOne_naturality O f

/-- The inverse components of the first-exterior-power isomorphisms form the inverse natural
transformation to the identity functor. -/
@[stacks 01CF "inverse first exterior power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    functor O 1 ⟶
      (𝟭 _ : PresheafOfModules.{w} (RingPresheaf O) ⥤
        PresheafOfModules.{w} (RingPresheaf O)) where
  app F := (degreeOneIso O F).inv
  naturality _ _ f := degreeOneIso_inv_naturality O f

/-- A component of the forward degree-one natural transformation is the canonical degree-one
map. -/
@[simp, stacks 01CF "forward first exterior power natural transformation component"]
theorem degreeOneNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeOneNatTrans O).app F = degreeOne O F := sorry

/-- A component of the inverse degree-one natural transformation is the inverse objectwise
first-exterior-power map. -/
@[simp, stacks 01CF "inverse first exterior power natural transformation component"]
theorem degreeOneInvNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeOneInvNatTrans O).app F = (degreeOneIso O F).inv := sorry

/-- The forward first-exterior-power natural transformation followed by its inverse is the
identity transformation. -/
@[simp, stacks 01CF "first exterior power natural transformation forward-inverse law"]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans O ≫ degreeOneInvNatTrans O = 𝟙 _ := sorry

/-- The inverse first-exterior-power natural transformation followed by the forward one is the
identity transformation. -/
@[simp, stacks 01CF "first exterior power natural transformation inverse-forward law"]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans O ≫ degreeOneNatTrans O = 𝟙 _ := sorry

/-- Module presheaves are naturally isomorphic to their first exterior powers. -/
@[stacks 01CF "natural first exterior power of module presheaves"]
noncomputable def degreeOneNatIso :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf O) ⥤
      PresheafOfModules.{w} (RingPresheaf O)) ≅ functor O 1 :=
  { hom := degreeOneNatTrans O
    inv := degreeOneInvNatTrans O
    hom_inv_id := degreeOneNatTrans_hom_inv_id O
    inv_hom_id := degreeOneNatTrans_inv_hom_id O }

/-- A component of `degreeOneNatIso` is the objectwise first-exterior-power isomorphism. -/
@[simp, stacks 01CF "first exterior power natural isomorphism component"]
theorem degreeOneNatIso_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeOneNatIso O).app F = degreeOneIso O F := sorry

/-- The forward natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom"]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso O).hom = degreeOneNatTrans O := sorry

/-- The inverse natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse"]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso O).inv = degreeOneInvNatTrans O := sorry

/-- The forward component of `degreeOneNatIso` is the canonical degree-one map. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom component"]
theorem degreeOneNatIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeOneNatIso O).hom.app F = degreeOne O F := sorry

/-- The inverse component of `degreeOneNatIso` is the inverse objectwise isomorphism. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse component"]
theorem degreeOneNatIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeOneNatIso O).inv.app F = (degreeOneIso O F).inv := sorry

end PresheafOfModules.ExteriorPower

