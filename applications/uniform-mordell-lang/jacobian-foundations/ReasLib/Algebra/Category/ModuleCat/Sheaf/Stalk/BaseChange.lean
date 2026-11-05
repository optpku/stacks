module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of scalar extension for sheaves of modules

This file compares extension of scalars on stalks with the stalk of the canonical explicit
pullback construction.  Its public comparison is stated directly using
`PresheafOfModules.pullback` and `PresheafOfModules.sheafification`; it introduces no second
named owner for that composite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Sheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable (ℱ : SheafOfModules (ringSheafOfComm 𝒪))
variable (x : X)

/-- The module stalk underlying the explicit sheaf extension of scalars of `ℱ` along `p`. -/
noncomputable abbrev sheafModuleBaseChangeTarget : ModuleCat (𝒪'.presheaf.stalk x) :=
  ModuleCat.of (𝒪'.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
        ((PresheafOfModules.pullback
          (TopCat.Presheaf.commRingPresheafHomOverId p.hom)).obj ℱ.val)).val.presheaf x)

/-
Mathlib owns the presheaf comparison as `TopCat.Presheaf.stalkBaseChangeComparison` and owns
module sheafification through `PresheafOfModules.sheafification`. The source tensor-product sheaf
is therefore represented by that canonical composite construction. The comparison below composes
the presheaf base-change map with the sheafification unit on stalks; its target is restricted along
the stalk map of `𝟙 𝒪'.obj`, so it is canonically an `𝒪'_x`-module without introducing a duplicate
module structure or a choice-based isomorphism.
-/

/-- The canonical comparison from the extended-scalar stalk of `ℱ` to the stalk of its sheaf
extension of scalars. -/
noncomputable def sheafModuleBaseChangeComparison :
    (ModuleCat.extendScalars
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
        (ModuleCat.of (𝒪.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) ⟶
      (ModuleCat.restrictScalars
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map (𝟙 𝒪'.obj)).hom)).obj
          (sheafModuleBaseChangeTarget p ℱ x) :=
  TopCat.Presheaf.stalkBaseChangeComparison p.hom ℱ.val x ≫
    TopCat.Presheaf.stalkModuleMapToRestrict (𝟙 𝒪'.obj)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
        ((PresheafOfModules.pullback
          (TopCat.Presheaf.commRingPresheafHomOverId p.hom)).obj ℱ.val)) x

/-- The normalized comparison from extension of scalars on the stalk of `ℱ` to the ordinary
`𝒪'_x`-module stalk of its explicit sheaf extension of scalars. -/
@[stacks 0D09 "module base-change stalk comparison"]
noncomputable def moduleBaseChangeStalkComparison :
    (ModuleCat.extendScalars
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
        (ModuleCat.of (𝒪.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) ⟶
      sheafModuleBaseChangeTarget p ℱ x :=
  TopCat.Presheaf.stalkBaseChangeComparison p.hom ℱ.val x ≫
    moduleSheafificationStalkComparison 𝒪'
      ((PresheafOfModules.pullback
        (TopCat.Presheaf.commRingPresheafHomOverId p.hom)).obj ℱ.val) x

/-- The explicit inverse from the stalk of the extended module sheaf to extension of scalars on
the original stalk. -/
@[stacks 0D09 "inverse module base-change stalk comparison"]
noncomputable def moduleBaseChangeStalkComparisonInv :
    sheafModuleBaseChangeTarget p ℱ x ⟶
      (ModuleCat.extendScalars
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
          (ModuleCat.of (𝒪.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) :=
  moduleSheafificationStalkComparisonInv 𝒪'
      ((PresheafOfModules.pullback
        (TopCat.Presheaf.commRingPresheafHomOverId p.hom)).obj ℱ.val) x ≫
    TopCat.Presheaf.stalkBaseChangeComparisonInv p.hom ℱ.val x

/-- The normalized base-change comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem moduleBaseChangeStalkComparison_hom_inv_id :
    moduleBaseChangeStalkComparison p ℱ x ≫
      moduleBaseChangeStalkComparisonInv p ℱ x = 𝟙 _ := sorry

/-- The explicit inverse followed by the normalized base-change comparison is the identity. -/
@[simp]
theorem moduleBaseChangeStalkComparison_inv_hom_id :
    moduleBaseChangeStalkComparisonInv p ℱ x ≫
      moduleBaseChangeStalkComparison p ℱ x = 𝟙 _ := sorry

/-- The normalized canonical isomorphism between extension of scalars on a module-sheaf stalk
and the stalk of the extended module sheaf. -/
@[stacks 0D09 "module base-change stalk isomorphism"]
noncomputable def moduleBaseChangeStalkComparisonIso :
    (ModuleCat.extendScalars
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
        (ModuleCat.of (𝒪.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) ≅
      sheafModuleBaseChangeTarget p ℱ x where
  hom := moduleBaseChangeStalkComparison p ℱ x
  inv := moduleBaseChangeStalkComparisonInv p ℱ x
  hom_inv_id := moduleBaseChangeStalkComparison_hom_inv_id p ℱ x
  inv_hom_id := moduleBaseChangeStalkComparison_inv_hom_id p ℱ x

/-- The normalized comparison between extension of scalars on a module-sheaf stalk and the stalk
of the extended module sheaf is an isomorphism. -/
@[stacks 0D09 "module base-change stalk comparison is an isomorphism", instance]
instance moduleBaseChangeStalkComparison_isIso :
    IsIso (moduleBaseChangeStalkComparison p ℱ x) := sorry

/-- The explicit inverse of the identity-restricted sheaf base-change comparison. -/
noncomputable def sheafModuleBaseChangeComparisonInv :
    (ModuleCat.restrictScalars
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map (𝟙 𝒪'.obj)).hom)).obj
        (sheafModuleBaseChangeTarget p ℱ x) ⟶
      (ModuleCat.extendScalars
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
          (ModuleCat.of (𝒪.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) :=
  (ModuleCat.restrictScalarsId'
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map (𝟙 𝒪'.obj)).hom)
      (congrArg CommRingCat.Hom.hom
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_id 𝒪'.obj))).hom.app _ ≫
    moduleBaseChangeStalkComparisonInv p ℱ x

/-- The identity-restricted comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem sheafModuleBaseChangeComparison_hom_inv_id :
    sheafModuleBaseChangeComparison p ℱ x ≫
      sheafModuleBaseChangeComparisonInv p ℱ x = 𝟙 _ := sorry

/-- The explicit inverse followed by the identity-restricted comparison is the identity. -/
@[simp]
theorem sheafModuleBaseChangeComparison_inv_hom_id :
    sheafModuleBaseChangeComparisonInv p ℱ x ≫
      sheafModuleBaseChangeComparison p ℱ x = 𝟙 _ := sorry

/-- The canonical isomorphism before normalizing restriction along the identity stalk map. -/
noncomputable def sheafModuleBaseChangeComparisonIso :
    (ModuleCat.extendScalars
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
        (ModuleCat.of (𝒪.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x)) ≅
      (ModuleCat.restrictScalars
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map (𝟙 𝒪'.obj)).hom)).obj
          (sheafModuleBaseChangeTarget p ℱ x) where
  hom := sheafModuleBaseChangeComparison p ℱ x
  inv := sheafModuleBaseChangeComparisonInv p ℱ x
  hom_inv_id := sheafModuleBaseChangeComparison_hom_inv_id p ℱ x
  inv_hom_id := sheafModuleBaseChangeComparison_inv_hom_id p ℱ x

/-- The identity-restricted sheaf base-change comparison is an isomorphism. -/
instance sheafModuleBaseChangeComparison_isIso :
    IsIso (sheafModuleBaseChangeComparison p ℱ x) := sorry

/-- The forward map of `sheafModuleBaseChangeComparisonIso` is the canonical sheaf base-change
comparison. -/
@[simp]
theorem sheafModuleBaseChangeComparisonIso_hom :
    (sheafModuleBaseChangeComparisonIso p ℱ x).hom =
      sheafModuleBaseChangeComparison p ℱ x := sorry

/-- The inverse map of the identity-restricted base-change isomorphism is explicit. -/
@[simp]
theorem sheafModuleBaseChangeComparisonIso_inv :
    (sheafModuleBaseChangeComparisonIso p ℱ x).inv =
      sheafModuleBaseChangeComparisonInv p ℱ x := sorry

/-- The forward map of the normalized base-change isomorphism is the canonical comparison. -/
@[simp]
theorem moduleBaseChangeStalkComparisonIso_hom :
    (moduleBaseChangeStalkComparisonIso p ℱ x).hom =
      moduleBaseChangeStalkComparison p ℱ x := sorry

/-- The inverse map of the normalized base-change isomorphism is explicit. -/
@[simp]
theorem moduleBaseChangeStalkComparisonIso_inv :
    (moduleBaseChangeStalkComparisonIso p ℱ x).inv =
      moduleBaseChangeStalkComparisonInv p ℱ x := sorry

end TopCat.Sheaf
