/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# First symmetric powers of module presheaves

The sectionwise maps from a module presheaf to its first symmetric-power presheaf are assembled
from the canonical objectwise isomorphisms in `ModuleCat`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The objectwise first-symmetric-power isomorphisms commute with restriction. -/
@[stacks 01CF "sectionwise first symmetric power naturality"]
theorem degreeOneIso_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫
        (ModuleCat.restrictScalars ((RingPresheaf 𝒪).map f).hom).map
          (ModuleCat.symmetricPower.degreeOneIso (sectionObj 𝒪 F V)).hom =
      (ModuleCat.symmetricPower.degreeOneIso (sectionObj 𝒪 F U)).hom ≫
        (presheaf 𝒪 F 1).map f := sorry

/-- A module presheaf is canonically isomorphic to its first symmetric-power presheaf. -/
@[stacks 01CF "module presheaf as its first symmetric power"]
noncomputable def degreeOneIso
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    F ≅ presheaf 𝒪 F 1 :=
  PresheafOfModules.isoMk
    (fun U ↦ ModuleCat.symmetricPower.degreeOneIso (sectionObj 𝒪 F U))
    (fun _ _ f ↦ degreeOneIso_app_naturality 𝒪 F f)

/-- The canonical morphism from a module presheaf to its first symmetric power. -/
@[stacks 01CF "first symmetric power module-presheaf map"]
noncomputable def degreeOne
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    F ⟶ presheaf 𝒪 F 1 :=
  (degreeOneIso 𝒪 F).hom

/-- The forward component is the objectwise first-symmetric-power map. -/
@[simp, stacks 01CF "first symmetric power isomorphism hom component"]
theorem degreeOneIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (degreeOneIso 𝒪 F).hom.app U =
      (ModuleCat.symmetricPower.degreeOneIso (sectionObj 𝒪 F U)).hom := sorry

/-- The inverse component is the objectwise evaluation map. -/
@[simp, stacks 01CF "first symmetric power isomorphism inverse component"]
theorem degreeOneIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (degreeOneIso 𝒪 F).inv.app U =
      (ModuleCat.symmetricPower.degreeOneIso (sectionObj 𝒪 F U)).inv := sorry

/-- Restriction compatibility in terms of the canonical degree-one maps. -/
theorem degreeOne_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫
        (ModuleCat.restrictScalars (𝒪.map f).hom).map
          (ModuleCat.symmetricPower.degreeOne (sectionObj 𝒪 F V)) =
      ModuleCat.symmetricPower.degreeOne (sectionObj 𝒪 F U) ≫
        map 𝒪 F 1 f := sorry

/-- A component of the presheaf degree-one map is the module degree-one map. -/
@[simp, stacks 01CF "first symmetric power map component"]
theorem degreeOne_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (degreeOne 𝒪 F).app U =
      ModuleCat.symmetricPower.degreeOne (sectionObj 𝒪 F U) := sorry

/-- Degree-one symmetric-power maps are natural in the module presheaf. -/
@[reassoc, stacks 01CF "first symmetric power map naturality"]
theorem degreeOne_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    f ≫ degreeOne 𝒪 G = degreeOne 𝒪 F ≫ hom 𝒪 f 1 := sorry

/-- Naturality of inverse first-symmetric-power isomorphisms in a module presheaf. -/
@[stacks 01CF "inverse naturality of the first symmetric power"]
theorem degreeOneIso_inv_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    hom 𝒪 f 1 ≫ (degreeOneIso 𝒪 G).inv =
      (degreeOneIso 𝒪 F).inv ≫ f := sorry

/-- The degree-one maps form the forward natural transformation from the identity functor. -/
@[stacks 01CF "forward first symmetric power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (RingPresheaf 𝒪)) ⟶ functor 𝒪 1 where
  app F := degreeOne 𝒪 F
  naturality _ _ f := degreeOne_naturality 𝒪 f

/-- The inverse components form the reverse natural transformation to the identity functor. -/
@[stacks 01CF "inverse first symmetric power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    functor 𝒪 1 ⟶
      (𝟭 _ : PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
        PresheafOfModules.{w} (RingPresheaf 𝒪)) where
  app F := (degreeOneIso 𝒪 F).inv
  naturality _ _ f := degreeOneIso_inv_naturality 𝒪 f

/-- A component of the forward natural transformation is the canonical map. -/
@[simp, stacks 01CF "forward first symmetric power natural transformation component"]
theorem degreeOneNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeOneNatTrans 𝒪).app F = degreeOne 𝒪 F := sorry

/-- A component of the inverse natural transformation is the objectwise inverse map. -/
@[simp, stacks 01CF "inverse first symmetric power natural transformation component"]
theorem degreeOneInvNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeOneInvNatTrans 𝒪).app F = (degreeOneIso 𝒪 F).inv := sorry

/-- The forward first-symmetric-power transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "first symmetric power natural transformation forward-inverse law"]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans 𝒪 ≫ degreeOneInvNatTrans 𝒪 = 𝟙 _ := sorry

/-- The inverse first-symmetric-power transformation followed by the forward one is the identity. -/
@[simp, stacks 01CF "first symmetric power natural transformation inverse-forward law"]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans 𝒪 ≫ degreeOneNatTrans 𝒪 = 𝟙 _ := sorry

/-- Module presheaves are naturally isomorphic to their first symmetric powers. -/
@[stacks 01CF "natural first symmetric power of module presheaves"]
noncomputable def degreeOneNatIso :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (RingPresheaf 𝒪)) ≅ functor 𝒪 1 :=
  { hom := degreeOneNatTrans 𝒪
    inv := degreeOneInvNatTrans 𝒪
    hom_inv_id := degreeOneNatTrans_hom_inv_id 𝒪
    inv_hom_id := degreeOneNatTrans_inv_hom_id 𝒪 }

/-- A component of `degreeOneNatIso` is the objectwise degree-one isomorphism. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism component"]
theorem degreeOneNatIso_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeOneNatIso 𝒪).app F = degreeOneIso 𝒪 F := sorry

/-- The forward natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism hom"]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso 𝒪).hom = degreeOneNatTrans 𝒪 := sorry

/-- The inverse natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism inverse"]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso 𝒪).inv = degreeOneInvNatTrans 𝒪 := sorry

/-- The forward component of `degreeOneNatIso` is the canonical degree-one map. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism hom component"]
theorem degreeOneNatIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeOneNatIso 𝒪).hom.app F = degreeOne 𝒪 F := sorry

/-- The inverse component of `degreeOneNatIso` is the objectwise inverse isomorphism. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism inverse component"]
theorem degreeOneNatIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeOneNatIso 𝒪).inv.app F = (degreeOneIso 𝒪 F).inv := sorry

end PresheafOfModules.SymmetricPower
