module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
public import ReasLib.CategoryTheory.Adjunction.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective module sheaves on localized sites

Restriction to a slice site is the right adjoint of exact extension from the slice.  It therefore
preserves injective module sheaves.  This file records that fact on the canonical localization
functor, independently of any presentation by raw pushforward data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)

/-- Restriction of module sheaves to a slice site preserves injective objects. -/
@[stacks 03F3 "localized restriction preserves injectives", instance]
instance restriction_preservesInjectiveObjects
    [restrictionIsRightAdjoint : (restriction R U : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (R.over U)).IsRightAdjoint] :
    (restriction R U : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (R.over U)).PreservesInjectiveObjects := sorry

/-- An injective module sheaf remains injective after restriction to a slice site. -/
@[stacks 03F3 "restriction of an injective module sheaf"]
theorem injective_restriction
    [restrictionIsRightAdjoint : (restriction R U : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (R.over U)).IsRightAdjoint]
    (I : SheafOfModules.{z} R) (hI : Injective I) :
    Injective ((restriction R U).obj I) := sorry

end SheafOfModules.Localization
