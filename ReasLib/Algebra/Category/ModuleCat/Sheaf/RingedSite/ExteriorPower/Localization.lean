module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior powers and localization of a ringed site

Restriction to a slice site commutes degreewise with exterior-power sheaves.  The comparison is
assembled from the topology-free presheaf comparison and the coefficient-generic compatibility
of module sheafification with slice restriction.
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
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Restriction to a slice commutes with the degree-`n` exterior-power sheaf. -/
@[stacks 01CG "exterior power and localized restriction"]
noncomputable def overIso (F : ringedSiteModuleCategory J O) (n : ℕ) :
    (sheaf O F n).over U ≅ sheaf (O.over U) (F.over U) n :=
  ModuleSheafification.overIso O U (presheaf O F n) ≪≫
    (moduleSheafification (O.over U)).mapIso
      (PresheafOfModules.ExteriorPower.overIso O.obj U F.val n)

/-- The exterior-power localization comparison is natural in the module sheaf. -/
@[stacks 01CG "exterior-power localization comparison naturality"]
theorem overIso_naturality
    (n : ℕ) {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (functor O n ⋙ Localization.restriction O U).map f ≫
        (overIso O U G n).hom =
      (overIso O U F n).hom ≫
        (Localization.restriction O U ⋙ functor (O.over U) n).map f := sorry

/-- The inverse exterior-power localization comparison is natural in the module sheaf. -/
@[stacks 01CG "inverse exterior-power localization comparison naturality"]
theorem overIso_inv_naturality
    (n : ℕ) {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (Localization.restriction O U ⋙ functor (O.over U) n).map f ≫
        (overIso O U G n).inv =
      (overIso O U F n).inv ≫
        (functor O n ⋙ Localization.restriction O U).map f := sorry

/-- The forward degree-`n` exterior-power localization comparisons form a natural
transformation. -/
@[stacks 01CG "forward exterior-power localization comparison"]
noncomputable def overNatTrans (n : ℕ) :
    functor O n ⋙ Localization.restriction O U ⟶
      Localization.restriction O U ⋙ functor (O.over U) n where
  app F := (overIso O U F n).hom
  naturality _ _ f := overIso_naturality O U n f

/-- The inverse degree-`n` exterior-power localization comparisons form a natural
transformation. -/
@[stacks 01CG "inverse exterior-power localization comparison"]
noncomputable def overInvNatTrans (n : ℕ) :
    Localization.restriction O U ⋙ functor (O.over U) n ⟶
      functor O n ⋙ Localization.restriction O U where
  app F := (overIso O U F n).inv
  naturality _ _ f := overIso_inv_naturality O U n f

/-- A component of the forward degree-`n` exterior-power localization comparison is the
forward map of `overIso`. -/
@[simp, stacks 01CG "forward exterior-power localization comparison component"]
theorem overNatTrans_app (n : ℕ) (F : ringedSiteModuleCategory J O) :
    (overNatTrans O U n).app F = (overIso O U F n).hom := sorry

/-- A component of the inverse degree-`n` exterior-power localization comparison is the
inverse map of `overIso`. -/
@[simp, stacks 01CG "inverse exterior-power localization comparison component"]
theorem overInvNatTrans_app (n : ℕ) (F : ringedSiteModuleCategory J O) :
    (overInvNatTrans O U n).app F = (overIso O U F n).inv := sorry

/-- The forward exterior-power localization comparison followed by its inverse is the
identity. -/
@[simp, stacks 01CG "exterior-power localization comparison forward-inverse law"]
theorem overNatTrans_hom_inv_id (n : ℕ) :
    overNatTrans O U n ≫ overInvNatTrans O U n = 𝟙 _ := sorry

/-- The inverse exterior-power localization comparison followed by the forward comparison is
the identity. -/
@[simp, stacks 01CG "exterior-power localization comparison inverse-forward law"]
theorem overNatTrans_inv_hom_id (n : ℕ) :
    overInvNatTrans O U n ≫ overNatTrans O U n = 𝟙 _ := sorry

/-- Degree-`n` exterior-power sheaf formation commutes naturally with restriction to a slice. -/
@[stacks 01CG "natural exterior-power localization comparison"]
noncomputable def overNatIso (n : ℕ) :
    functor O n ⋙ Localization.restriction O U ≅
      Localization.restriction O U ⋙ functor (O.over U) n where
  hom := overNatTrans O U n
  inv := overInvNatTrans O U n
  hom_inv_id := overNatTrans_hom_inv_id O U n
  inv_hom_id := overNatTrans_inv_hom_id O U n

/-- The forward natural transformation of `overNatIso` is the explicit localization
comparison. -/
@[simp, stacks 01CG "exterior-power localization natural isomorphism hom"]
theorem overNatIso_hom (n : ℕ) :
    (overNatIso O U n).hom = overNatTrans O U n := sorry

/-- The inverse natural transformation of `overNatIso` is the explicit inverse localization
comparison. -/
@[simp, stacks 01CG "exterior-power localization natural isomorphism inverse"]
theorem overNatIso_inv (n : ℕ) :
    (overNatIso O U n).inv = overInvNatTrans O U n := sorry

/-- A component of `overNatIso` is the objectwise exterior-power localization isomorphism. -/
@[simp, stacks 01CG "exterior-power localization natural isomorphism component"]
theorem overNatIso_app (n : ℕ) (F : ringedSiteModuleCategory J O) :
    (overNatIso O U n).app F = overIso O U F n := sorry

/-- A forward component of `overNatIso` is the forward objectwise localization comparison. -/
@[simp, stacks 01CG "exterior-power localization natural isomorphism hom component"]
theorem overNatIso_hom_app (n : ℕ) (F : ringedSiteModuleCategory J O) :
    (overNatIso O U n).hom.app F = (overIso O U F n).hom := sorry

/-- An inverse component of `overNatIso` is the inverse objectwise localization comparison. -/
@[simp, stacks 01CG "exterior-power localization natural isomorphism inverse component"]
theorem overNatIso_inv_app (n : ℕ) (F : ringedSiteModuleCategory J O) :
    (overNatIso O U n).inv.app F = (overIso O U F n).inv := sorry

end SheafOfModules.RingedSite.ExteriorPower
