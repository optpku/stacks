module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.Picard
import Mathlib.Tactic.CrossRefAttribute

/-!
# Picard groups of ringed sites

This file specializes the Picard group of a monoidal category to module sheaves over a
commutative ring sheaf.  The representation and its generic API remain owned by
`MonoidalCategory.PicardGroup`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{w})
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The Picard group of a commutative ring sheaf on a site. -/
@[stacks 040C "Picard group of a ringed site"]
abbrev PicardGroup :=
  MonoidalCategory.PicardGroup (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)

/-- Notation for the Picard group of a ring sheaf. -/
scoped[RingedSitePicard] notation:max "Pic(" 𝒪 ")" =>
  SheafOfModules.RingedSite.PicardGroup _ 𝒪

namespace PicardGroup

/-- The Picard class represented by the structure module of a ringed site. -/
noncomputable def unitModuleClass : PicardGroup J 𝒪 :=
  @MonoidalCategory.PicardGroup.mk
    (ringedSiteModuleCategory J 𝒪) _ _ (unitModule J 𝒪)
      (unitModuleIsInvertible (J := J) (𝒪 := 𝒪))

/-- The structure module represents the zero Picard class. -/
theorem unitModuleClass_eq_zero :
    unitModuleClass J 𝒪 = 0 := sorry

/-- An invertible module represents zero exactly when it is isomorphic to the structure module. -/
theorem mk_eq_zero_iff_unitModule
    (L : ringedSiteModuleCategory J 𝒪) [isInvertibleObject L] :
    (MonoidalCategory.PicardGroup.mk L : PicardGroup J 𝒪) = 0 ↔
      Nonempty (L ≅ unitModule J 𝒪) := sorry

variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

/-- The negative of the class of an invertible module is represented by its internal-Hom dual. -/
theorem mk_internalHom_unit
    (L : ringedSiteModuleCategory J 𝒪) [isInvertibleObject L] :
    (MonoidalCategory.PicardGroup.mk (dual L) : PicardGroup J 𝒪) =
      -MonoidalCategory.PicardGroup.mk L := sorry

end PicardGroup

end SheafOfModules.RingedSite
