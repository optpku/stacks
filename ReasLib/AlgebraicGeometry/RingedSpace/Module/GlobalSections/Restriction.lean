/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections with restricted scalars

This file packages the ordinary global-sections functor after restriction of scalars along a map
into the global-sections ring. It is the canonical right-hand side of associated-sheaf Hom APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {R : Type u} [CommRing R]

/-- Global sections of module sheaves, regarded as `R`-modules through
`alpha : R →+* Γ(X, O_X)`. -/
noncomputable abbrev moduleGlobalSectionsRestrictionFunctor (X : RingedSpace.{u})
    (alpha : R →+* globalSectionsRing X) : X.Modules ⥤ ModuleCat.{u} R :=
  moduleGlobalSectionsFunctor X ⋙ ModuleCat.restrictScalars alpha

/-- The `R`-module of global sections of `G`, with scalars restricted along `alpha`. -/
noncomputable abbrev moduleGlobalSectionsRestriction (X : RingedSpace.{u})
    (alpha : R →+* globalSectionsRing X) (G : X.Modules) : ModuleCat.{u} R :=
  (moduleGlobalSectionsRestrictionFunctor X alpha).obj G

namespace moduleGlobalSectionsRestrictionFunctor

/-- Restricting global sections along the identity scalar map recovers ordinary global
sections. -/
@[stacks 01BH "identity global sections comparison"]
noncomputable def idIso (X : RingedSpace.{u}) :
    moduleGlobalSectionsRestrictionFunctor X (RingHom.id (globalSectionsRing X)) ≅
      moduleGlobalSectionsFunctor X :=
  Functor.isoWhiskerLeft (moduleGlobalSectionsFunctor X)
      (ModuleCat.restrictScalarsId (globalSectionsRing X)) ≪≫
    Functor.rightUnitor (moduleGlobalSectionsFunctor X)

end moduleGlobalSectionsRestrictionFunctor



end AlgebraicGeometry.RingedSpace
