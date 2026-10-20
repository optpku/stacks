/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Restriction

/-!
# Germs of global sections of module sheaves

This file owns the canonical map from global sections to a stalk and its module-valued analogue.
The latter is packaged both objectwise and as a natural transformation after restriction of
scalars.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- The ring map from global scalars to the stalk at `x`, after a chosen map into global
sections. -/
@[stacks 01BH "global sections to stalk"]
noncomputable abbrev globalSectionsToStalk
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    R →+* X.presheaf.stalk x :=
  (X.presheaf.Γgerm x).hom.comp alpha

/-- Taking the germ of a global module section is semilinear for
`globalSectionsToStalk alpha x`. -/
theorem moduleGlobalSectionsToStalk_smul
    (alpha : R →+* X.globalSectionsRing) (G : X.Modules) (x : X)
    (r : R) (m : X.moduleGlobalSectionsRestriction alpha G) :
    TopCat.Presheaf.Γgerm G.val.presheaf x (r • m) =
      globalSectionsToStalk alpha x r •
        TopCat.Presheaf.Γgerm G.val.presheaf x m := sorry

/-- The germ morphism from global sections of `G`, with scalars restricted along `alpha`, to the
stalk of `G`, with scalars restricted along `globalSectionsToStalk alpha x`. -/
noncomputable def moduleGlobalSectionsToStalk
    (alpha : R →+* X.globalSectionsRing) (G : X.Modules) (x : X) :
    X.moduleGlobalSectionsRestriction alpha G ⟶
      (ModuleCat.restrictScalars (globalSectionsToStalk alpha x)).obj
        (X.stalkModuleCat G x) :=
  (ModuleCat.semilinearMapAddEquiv (globalSectionsToStalk alpha x)
    (X.moduleGlobalSectionsRestriction alpha G) (X.stalkModuleCat G x))
    { toFun := TopCat.Presheaf.Γgerm G.val.presheaf x
      map_add' := (TopCat.Presheaf.Γgerm G.val.presheaf x).hom.map_add
      map_smul' := moduleGlobalSectionsToStalk_smul alpha G x }

/-- The global-to-stalk germ morphisms are natural in the module sheaf. -/
theorem moduleGlobalSectionsToStalk_naturality
    (alpha : R →+* X.globalSectionsRing) (x : X)
    {G H : X.Modules} (f : G ⟶ H) :
    (X.moduleGlobalSectionsRestrictionFunctor alpha).map f ≫
        moduleGlobalSectionsToStalk alpha H x =
      moduleGlobalSectionsToStalk alpha G x ≫
        (ModuleCat.restrictScalars (globalSectionsToStalk alpha x)).map
          ((X.stalkModuleFunctor x).map f) := sorry

/-- Taking the germ defines a natural transformation from restricted global sections to the
restricted stalk functor. -/
@[stacks 01BH "global sections to stalk natural transformation"]
noncomputable def moduleGlobalSectionsToStalkNatTrans
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    X.moduleGlobalSectionsRestrictionFunctor alpha ⟶
      X.stalkModuleFunctor x ⋙
        ModuleCat.restrictScalars (globalSectionsToStalk alpha x) where
  app G := moduleGlobalSectionsToStalk alpha G x
  naturality _ _ f := moduleGlobalSectionsToStalk_naturality alpha x f

end AlgebraicGeometry.RingedSpace
