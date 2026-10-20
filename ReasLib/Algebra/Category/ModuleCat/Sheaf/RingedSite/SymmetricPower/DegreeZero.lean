/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeroth symmetric powers of module sheaves

The sectionwise zeroth-symmetric-power isomorphism is transported through module sheafification.
Its inverse is the existing symmetric unit, so the degree identification and multiplication API
share one canonical unit map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The zeroth symmetric-power sheaf is canonically the structure module. -/
@[stacks 01CF "zeroth symmetric power of module sheaves"]
noncomputable def degreeZeroIso (F : ringedSiteModuleCategory J 𝒪) :
    sheaf 𝒪 F 0 ≅ unitModule J 𝒪 :=
  (moduleSheafification 𝒪).mapIso
      (PresheafOfModules.SymmetricPower.degreeZeroIso 𝒪.obj F.val) ≪≫
    moduleSheafificationValIso 𝒪 (unitModule J 𝒪)

/-- The canonical projection from the zeroth symmetric-power sheaf to the structure module. -/
@[stacks 01CF "zeroth symmetric power sheaf projection"]
noncomputable def degreeZero (F : ringedSiteModuleCategory J 𝒪) :
    sheaf 𝒪 F 0 ⟶ unitModule J 𝒪 :=
  (degreeZeroIso 𝒪 F).hom

/-- The forward map of the zeroth-symmetric-power isomorphism is `degreeZero`. -/
@[simp, stacks 01CF "zeroth symmetric power isomorphism hom"]
theorem degreeZeroIso_hom (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroIso 𝒪 F).hom = degreeZero 𝒪 F := sorry

/-- The inverse zeroth-symmetric-power isomorphism is the symmetric unit. -/
@[simp, stacks 01CF "zeroth symmetric power isomorphism inverse"]
theorem degreeZeroIso_inv (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroIso 𝒪 F).inv = one 𝒪 F := sorry

/-- The degree-zero symmetric unit is canonically an isomorphism. -/
instance one_isIso (F : ringedSiteModuleCategory J 𝒪) :
    IsIso (one 𝒪 F) := sorry

/-- Zeroth symmetric-power projections are natural in the module sheaf. -/
@[reassoc, stacks 01CF "zeroth symmetric power map naturality"]
theorem degreeZero_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    map 𝒪 f 0 ≫ degreeZero 𝒪 G = degreeZero 𝒪 F := sorry

/-- Naturality of the zeroth-symmetric-power identification. -/
@[stacks 01CF "zeroth symmetric power identification naturality for module sheaves"]
theorem degreeZeroIso_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    (functor 𝒪 0).map f ≫ (degreeZeroIso 𝒪 G).hom =
      (degreeZeroIso 𝒪 F).hom ≫
        ((Functor.const _).obj (unitModule J 𝒪)).map f := sorry

/-- Naturality of the inverse zeroth-symmetric-power identification. -/
@[stacks 01CF "inverse zeroth symmetric power identification naturality for module sheaves"]
theorem degreeZeroIso_inv_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    ((Functor.const _).obj (unitModule J 𝒪)).map f ≫
        (degreeZeroIso 𝒪 G).inv =
      (degreeZeroIso 𝒪 F).inv ≫ (functor 𝒪 0).map f := sorry

/-- The degree-zero maps form the forward natural transformation to the structure module. -/
@[stacks 01CF "forward zeroth symmetric power natural transformation for module sheaves"]
noncomputable def degreeZeroNatTrans :
    functor 𝒪 0 ⟶ (Functor.const _).obj (unitModule J 𝒪) where
  app F := (degreeZeroIso 𝒪 F).hom
  naturality _ _ f := degreeZeroIso_naturality 𝒪 f

/-- The inverse degree-zero components form the reverse natural transformation. -/
@[stacks 01CF "inverse zeroth symmetric power natural transformation for module sheaves"]
noncomputable def degreeZeroInvNatTrans :
    (Functor.const _).obj (unitModule J 𝒪) ⟶ functor 𝒪 0 where
  app F := (degreeZeroIso 𝒪 F).inv
  naturality _ _ f := degreeZeroIso_inv_naturality 𝒪 f

/-- A component of the forward natural transformation is `degreeZero`. -/
@[simp, stacks 01CF "forward zeroth symmetric power natural transformation component"]
theorem degreeZeroNatTrans_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroNatTrans 𝒪).app F = degreeZero 𝒪 F := sorry

/-- A component of the inverse natural transformation is the symmetric unit. -/
@[simp, stacks 01CF "inverse zeroth symmetric power natural transformation component"]
theorem degreeZeroInvNatTrans_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroInvNatTrans 𝒪).app F = (degreeZeroIso 𝒪 F).inv := sorry

/-- The forward degree-zero natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "zeroth symmetric power natural transformation forward-inverse law"]
theorem degreeZeroNatTrans_hom_inv_id :
    degreeZeroNatTrans 𝒪 ≫ degreeZeroInvNatTrans 𝒪 = 𝟙 _ := sorry

/-- The inverse degree-zero natural transformation followed by the forward one is the identity. -/
@[simp, stacks 01CF "zeroth symmetric power natural transformation inverse-forward law"]
theorem degreeZeroNatTrans_inv_hom_id :
    degreeZeroInvNatTrans 𝒪 ≫ degreeZeroNatTrans 𝒪 = 𝟙 _ := sorry

/-- Zeroth symmetric powers are naturally the constant structure-module functor. -/
@[stacks 01CF "natural zeroth symmetric power of module sheaves"]
noncomputable def degreeZeroNatIso :
    functor 𝒪 0 ≅ (Functor.const _).obj (unitModule J 𝒪) :=
  { hom := degreeZeroNatTrans 𝒪
    inv := degreeZeroInvNatTrans 𝒪
    hom_inv_id := degreeZeroNatTrans_hom_inv_id 𝒪
    inv_hom_id := degreeZeroNatTrans_inv_hom_id 𝒪 }

/-- The forward transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth symmetric power natural isomorphism hom"]
theorem degreeZeroNatIso_hom :
    (degreeZeroNatIso 𝒪).hom = degreeZeroNatTrans 𝒪 := sorry

/-- The inverse transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth symmetric power natural isomorphism inverse"]
theorem degreeZeroNatIso_inv :
    (degreeZeroNatIso 𝒪).inv = degreeZeroInvNatTrans 𝒪 := sorry

/-- A component of `degreeZeroNatIso` is the objectwise degree-zero isomorphism. -/
@[simp, stacks 01CF "zeroth symmetric power natural isomorphism component"]
theorem degreeZeroNatIso_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroNatIso 𝒪).app F = degreeZeroIso 𝒪 F := sorry

/-- The forward component of `degreeZeroNatIso` is `degreeZero`. -/
@[simp, stacks 01CF "zeroth symmetric power natural isomorphism hom component"]
theorem degreeZeroNatIso_hom_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroNatIso 𝒪).hom.app F = degreeZero 𝒪 F := sorry

/-- The inverse component of `degreeZeroNatIso` is the symmetric unit. -/
@[simp, stacks 01CF "zeroth symmetric power natural isomorphism inverse component"]
theorem degreeZeroNatIso_inv_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeZeroNatIso 𝒪).inv.app F = (degreeZeroIso 𝒪 F).inv := sorry

end SheafOfModules.RingedSite.SymmetricPower
