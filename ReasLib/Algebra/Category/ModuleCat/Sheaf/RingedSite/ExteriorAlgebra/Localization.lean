/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior algebras and localization of a ringed site

Restriction to a slice site commutes with the exterior-algebra sheaf functor.  The comparison is
the composite of the topology-free sectionwise comparison and the canonical compatibility of
module sheafification with slice restriction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- 01CF: Restriction to a slice commutes with the exterior-algebra sheaf construction. -/
@[stacks 01CF "exterior algebra and localized restriction"]
noncomputable def overIso (F : ringedSiteModuleCategory J O) :
    (sheaf O F).over U ≅ sheaf (O.over U) (F.over U) :=
  ModuleSheafification.overIso O U (presheaf O F) ≪≫
    (moduleSheafification (O.over U)).mapIso
      (PresheafOfModules.ExteriorAlgebra.overIso O.obj U F.val)

/-- The localization comparison preserves the degree-one exterior-algebra generator. -/
@[stacks 01CF "localized exterior-algebra generator"]
theorem overIso_hom_ι (F : ringedSiteModuleCategory J O) :
    (SheafOfModules.Hom.over (ι O F) U) ≫ (overIso O U F).hom =
      ι (O.over U) (F.over U) := sorry

/-- The inverse exterior-algebra localization comparison carries the degree-one generator on the
slice back to the restricted global generator. -/
@[stacks 01CF "inverse localized exterior-algebra generator"]
theorem overIso_inv_ι (F : ringedSiteModuleCategory J O) :
    ι (O.over U) (F.over U) ≫ (overIso O U F).inv =
      SheafOfModules.Hom.over (ι O F) U := sorry

/-- The exterior-algebra localization comparison is natural in the module sheaf. -/
@[stacks 01CF "exterior-algebra localization comparison naturality"]
theorem overIso_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (functor O ⋙ Localization.restriction O U).map f ≫
        (overIso O U G).hom =
      (overIso O U F).hom ≫
        (Localization.restriction O U ⋙ functor (O.over U)).map f := sorry

/-- The inverse exterior-algebra localization comparison is natural in the module sheaf. -/
@[stacks 01CF "inverse naturality of the exterior-algebra localization comparison"]
theorem overIso_inv_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (Localization.restriction O U ⋙ functor (O.over U)).map f ≫
        (overIso O U G).inv =
      (overIso O U F).inv ≫
        (functor O ⋙ Localization.restriction O U).map f := sorry

/-- The forward exterior-algebra localization comparisons form a natural transformation. -/
@[stacks 01CF "forward exterior-algebra localization comparison"]
noncomputable def overNatTrans :
    functor O ⋙ Localization.restriction O U ⟶
      Localization.restriction O U ⋙ functor (O.over U) where
  app F := (overIso O U F).hom
  naturality _ _ f := overIso_naturality O U f

/-- The inverse exterior-algebra localization comparisons form a natural transformation. -/
@[stacks 01CF "inverse exterior-algebra localization comparison"]
noncomputable def overInvNatTrans :
    Localization.restriction O U ⋙ functor (O.over U) ⟶
      functor O ⋙ Localization.restriction O U where
  app F := (overIso O U F).inv
  naturality _ _ f := overIso_inv_naturality O U f

/-- A component of the forward exterior-algebra localization comparison is the forward map of
`overIso`. -/
@[simp, stacks 01CF "forward exterior-algebra localization comparison component"]
theorem overNatTrans_app (F : ringedSiteModuleCategory J O) :
    (overNatTrans O U).app F = (overIso O U F).hom := sorry

/-- A component of the inverse exterior-algebra localization comparison is the inverse map of
`overIso`. -/
@[simp, stacks 01CF "inverse exterior-algebra localization comparison component"]
theorem overInvNatTrans_app (F : ringedSiteModuleCategory J O) :
    (overInvNatTrans O U).app F = (overIso O U F).inv := sorry

/-- The forward exterior-algebra localization comparison followed by its inverse is the identity. -/
@[simp, stacks 01CF "exterior-algebra localization comparison forward-inverse law"]
theorem overNatTrans_hom_inv_id :
    overNatTrans O U ≫ overInvNatTrans O U = 𝟙 _ := sorry

/-- The inverse exterior-algebra localization comparison followed by the forward comparison is
the identity. -/
@[simp, stacks 01CF "exterior-algebra localization comparison inverse-forward law"]
theorem overNatTrans_inv_hom_id :
    overInvNatTrans O U ≫ overNatTrans O U = 𝟙 _ := sorry

/-- Exterior-algebra sheaf formation commutes naturally with restriction to a slice. -/
@[stacks 01CF "natural exterior-algebra localization comparison"]
noncomputable def overNatIso :
    functor O ⋙ Localization.restriction O U ≅
      Localization.restriction O U ⋙ functor (O.over U) where
  hom := overNatTrans O U
  inv := overInvNatTrans O U
  hom_inv_id := overNatTrans_hom_inv_id O U
  inv_hom_id := overNatTrans_inv_hom_id O U

/-- The forward natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra localization natural isomorphism hom"]
theorem overNatIso_hom :
    (overNatIso O U).hom = overNatTrans O U := sorry

/-- The inverse natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra localization natural isomorphism inverse"]
theorem overNatIso_inv :
    (overNatIso O U).inv = overInvNatTrans O U := sorry

/-- A component of `overNatIso` is the objectwise exterior-algebra localization isomorphism. -/
@[simp, stacks 01CF "exterior-algebra localization natural isomorphism component"]
theorem overNatIso_app (F : ringedSiteModuleCategory J O) :
    (overNatIso O U).app F = overIso O U F := sorry

/-- The forward component of `overNatIso` is the forward objectwise localization comparison. -/
@[simp, stacks 01CF "exterior-algebra localization natural isomorphism hom component"]
theorem overNatIso_hom_app (F : ringedSiteModuleCategory J O) :
    (overNatIso O U).hom.app F = (overIso O U F).hom := sorry

/-- The inverse component of `overNatIso` is the inverse objectwise localization comparison. -/
@[simp, stacks 01CF "exterior-algebra localization natural isomorphism inverse component"]
theorem overNatIso_inv_app (F : ringedSiteModuleCategory J O) :
    (overNatIso O U).inv.app F = (overIso O U F).inv := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
