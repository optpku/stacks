/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of module sections on a ringed site

The topology-independent construction is owned by `PresheafOfModules.BaseChange`.  This file
only transports it across the forgetful functor from module sheaves and converts an arrow of the
site to the corresponding arrow of the opposite category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w})
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Forget the sheaf condition while retaining the commutative coefficient-presheaf view. -/
abbrev forget :
    ringedSiteModuleCategory.{u, v, max w z, w} J O ⥤
      PresheafOfModules.{max w z} (ringPresheafOfComm O.obj) :=
  SheafOfModules.forget (ringSheaf J O)

/-- Evaluation of a module sheaf at `U`, obtained from presheaf evaluation after forgetting the
sheaf condition. -/
abbrev evaluation (U : C) :
    ringedSiteModuleCategory.{u, v, max w z, w} J O ⥤
      ModuleCat.{max w z} (O.obj.obj (op U)) :=
  forget O ⋙ PresheafOfModules.BaseChange.evaluation O.obj (op U)

/-- Evaluate over `V` and extend scalars along the restriction map associated to
`f : U ⟶ V`. -/
abbrev functor {U V : C} (f : U ⟶ V) :
    ringedSiteModuleCategory.{u, v, max w z, w} J O ⥤
      ModuleCat.{max w z} (O.obj.obj (op U)) :=
  forget O ⋙ PresheafOfModules.BaseChange.functor O.obj f.op

/-- Forgetting the sheaf condition preserves addition of module morphisms. -/
instance forget_additive : (forget.{u, v, w, z} O).Additive where
  map_add := by intros; rfl

/-- Evaluation of module sheaves preserves addition of morphisms. -/
instance evaluation_additive (U : C) : (evaluation.{u, v, w, z} O U).Additive where
  map_add := by intros; rfl

/-- Evaluation followed by extension of scalars preserves addition of morphisms. -/
instance functor_additive {U V : C} (f : U ⟶ V) :
    (functor.{u, v, w, z} O f).Additive where
  map_add {M N} a b := by
    change (ModuleCat.extendScalars.{w, w, max w z} ((O.obj.map f.op).hom)).map
        ((evaluation O V).map (a + b)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- The canonical base-change map from scalar-extended sections to sections over the target. -/
@[stacks 0GZN "module-sheaf base-change map"]
noncomputable abbrev map
    (M : ringedSiteModuleCategory.{u, v, max w z, w} J O)
    {U V : C} (f : U ⟶ V) :
    (functor O f).obj M ⟶ (evaluation O U).obj M :=
  PresheafOfModules.BaseChange.map O.obj M.val f.op

/-- The natural module-sheaf base-change comparison associated to
`f : U ⟶ V`. -/
@[stacks 0GZN "natural module-sheaf base-change comparison"]
noncomputable abbrev natTrans {U V : C} (f : U ⟶ V) :
    functor O f ⟶ evaluation O U :=
  Functor.whiskerLeft (forget O)
    (PresheafOfModules.BaseChange.natTrans O.obj f.op)

/-- The component of the sheaf-level natural transformation is its base-change map. -/
theorem natTrans_app
    (M : ringedSiteModuleCategory.{u, v, max w z, w} J O)
    {U V : C} (f : U ⟶ V) :
    (natTrans O f).app M = map O M f := sorry

/-- Base-change compatibility of a module sheaf, pulled back from the
canonical property of its underlying module presheaf. -/
@[stacks 0GZN "module-sheaf base-change compatibility"]
abbrev compatible :
    ObjectProperty (ringedSiteModuleCategory.{u, v, max w z, w} J O) :=
  (PresheafOfModules.BaseChange.compatible O.obj).inverseImage (forget O)

/-- A module sheaf is base-change compatible exactly when the comparison associated to every
arrow of the site is an isomorphism. -/
theorem compatible_iff
    (M : ringedSiteModuleCategory.{u, v, max w z, w} J O) :
    compatible O M ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (map O M f) := sorry

end SheafOfModules.RingedSite.BaseChange
