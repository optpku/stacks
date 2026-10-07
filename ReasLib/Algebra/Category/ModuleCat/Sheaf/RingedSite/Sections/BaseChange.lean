module

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

/-- Lemma 18.24.3 (0GZN): the module-sheaf component of the presheaf base-change map. -/
@[stacks 0GZN "module-sheaf base-change map"]
noncomputable abbrev map
    (M : ringedSiteModuleCategory.{u, v, max w z, w} J O)
    {U V : C} (f : U ⟶ V) :
    (functor O f).obj M ⟶ (evaluation O U).obj M :=
  PresheafOfModules.BaseChange.map O.obj M.val f.op

/-- Lemma 18.24.3 (0GZN): the natural module-sheaf base-change comparison associated to
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

/-- Lemma 18.24.3 (0GZN): base-change compatibility of a module sheaf, pulled back from the
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
