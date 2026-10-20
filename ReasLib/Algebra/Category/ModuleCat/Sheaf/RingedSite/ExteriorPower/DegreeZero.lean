/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction

/-!
# Zeroth exterior powers of module sheaves

The objectwise zeroth-exterior-power isomorphism is transported through module sheafification.
Its inverse is the existing exterior unit, so downstream constructions can use either the
isomorphism or the multiplication API without a comparison choice.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The zeroth exterior-power sheaf is canonically the structure module. -/
@[stacks 01CF "zeroth exterior power of module sheaves"]
noncomputable def degreeZeroIso (F : ringedSiteModuleCategory J O) :
    sheaf O F 0 ≅ unitModule J O :=
  (moduleSheafification O).mapIso
      (PresheafOfModules.ExteriorPower.degreeZeroIso O.obj F.val) ≪≫
    moduleSheafificationValIso O (unitModule J O)

/-- The canonical projection from the zeroth exterior-power sheaf to the structure module. -/
noncomputable def degreeZero (F : ringedSiteModuleCategory J O) :
    sheaf O F 0 ⟶ unitModule J O :=
  (degreeZeroIso O F).hom

/-- The forward map of the zeroth-exterior-power isomorphism is `degreeZero`. -/
@[simp]
theorem degreeZeroIso_hom (F : ringedSiteModuleCategory J O) :
    (degreeZeroIso O F).hom = degreeZero O F := sorry

/-- The inverse zeroth-exterior-power isomorphism is the exterior unit. -/
@[simp]
theorem degreeZeroIso_inv (F : ringedSiteModuleCategory J O) :
    (degreeZeroIso O F).inv = one O F := sorry

/-- The degree-zero exterior unit is canonically an isomorphism. -/
instance one_isIso (F : ringedSiteModuleCategory J O) :
    IsIso (one O F) := sorry

/-- Zeroth exterior-power projections are natural in the module sheaf. -/
@[reassoc]
theorem degreeZero_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    map O f 0 ≫ degreeZero O G = degreeZero O F := sorry

/-- Naturality of the zeroth-exterior-power identification. -/
@[stacks 01CF "zeroth exterior power identification naturality for module sheaves"]
theorem degreeZeroIso_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (functor O 0).map f ≫ (degreeZeroIso O G).hom =
      (degreeZeroIso O F).hom ≫
        ((Functor.const _).obj (unitModule J O)).map f := sorry

/-- Naturality of the inverse zeroth-exterior-power identification. -/
@[stacks 01CF "inverse zeroth exterior power identification naturality for module sheaves"]
theorem degreeZeroIso_inv_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    ((Functor.const _).obj (unitModule J O)).map f ≫
        (degreeZeroIso O G).inv =
      (degreeZeroIso O F).inv ≫ (functor O 0).map f := sorry

/-- The degree-zero exterior-power maps form the forward natural transformation to the
structure module. -/
@[stacks 01CF "forward zeroth exterior power natural transformation for module sheaves"]
noncomputable def degreeZeroNatTrans :
    functor O 0 ⟶ (Functor.const _).obj (unitModule J O) where
  app F := (degreeZeroIso O F).hom
  naturality _ _ f := degreeZeroIso_naturality O f

/-- The inverse components of the degree-zero exterior-power identifications form the inverse
natural transformation. -/
@[stacks 01CF "inverse zeroth exterior power natural transformation for module sheaves"]
noncomputable def degreeZeroInvNatTrans :
    (Functor.const _).obj (unitModule J O) ⟶ functor O 0 where
  app F := (degreeZeroIso O F).inv
  naturality _ _ f := degreeZeroIso_inv_naturality O f

/-- A component of the forward degree-zero natural transformation is `degreeZero`. -/
@[simp, stacks 01CF "forward zeroth exterior power natural transformation component"]
theorem degreeZeroNatTrans_app (F : ringedSiteModuleCategory J O) :
    (degreeZeroNatTrans O).app F = degreeZero O F := sorry

/-- A component of the inverse degree-zero natural transformation is the exterior unit. -/
@[simp, stacks 01CF "inverse zeroth exterior power natural transformation component"]
theorem degreeZeroInvNatTrans_app (F : ringedSiteModuleCategory J O) :
    (degreeZeroInvNatTrans O).app F = (degreeZeroIso O F).inv := sorry

/-- The forward degree-zero natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "zeroth exterior power natural transformation forward-inverse law"]
theorem degreeZeroNatTrans_hom_inv_id :
    degreeZeroNatTrans O ≫ degreeZeroInvNatTrans O = 𝟙 _ := sorry

/-- The inverse degree-zero natural transformation followed by its forward map is the identity. -/
@[simp, stacks 01CF "zeroth exterior power natural transformation inverse-forward law"]
theorem degreeZeroNatTrans_inv_hom_id :
    degreeZeroInvNatTrans O ≫ degreeZeroNatTrans O = 𝟙 _ := sorry

/-- Zeroth exterior powers are naturally the constant structure-module functor. -/
@[stacks 01CF "natural zeroth exterior power of module sheaves"]
noncomputable def degreeZeroNatIso :
    functor O 0 ≅ (Functor.const _).obj (unitModule J O) :=
  { hom := degreeZeroNatTrans O
    inv := degreeZeroInvNatTrans O
    hom_inv_id := degreeZeroNatTrans_hom_inv_id O
    inv_hom_id := degreeZeroNatTrans_inv_hom_id O }

/-- The forward natural transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism hom"]
theorem degreeZeroNatIso_hom :
    (degreeZeroNatIso O).hom = degreeZeroNatTrans O := sorry

/-- The inverse natural transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism inverse"]
theorem degreeZeroNatIso_inv :
    (degreeZeroNatIso O).inv = degreeZeroInvNatTrans O := sorry

/-- A component of `degreeZeroNatIso` is the objectwise zeroth-exterior-power isomorphism. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism component"]
theorem degreeZeroNatIso_app (F : ringedSiteModuleCategory J O) :
    (degreeZeroNatIso O).app F = degreeZeroIso O F := sorry

/-- The forward component of `degreeZeroNatIso` is `degreeZero`. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism hom component"]
theorem degreeZeroNatIso_hom_app (F : ringedSiteModuleCategory J O) :
    (degreeZeroNatIso O).hom.app F = degreeZero O F := sorry

/-- The inverse component of `degreeZeroNatIso` is the exterior unit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism inverse component"]
theorem degreeZeroNatIso_inv_app (F : ringedSiteModuleCategory J O) :
    (degreeZeroNatIso O).inv.app F = (degreeZeroIso O F).inv := sorry

end SheafOfModules.RingedSite.ExteriorPower

