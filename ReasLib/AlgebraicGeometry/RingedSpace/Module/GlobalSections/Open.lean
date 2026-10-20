module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of global module sections to an open subset

A map from a coefficient ring into global functions induces compatible scalar maps to every open
subset. This leaf packages both the ring maps and restriction of module sections, objectwise and
as a natural transformation.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- Restrict a chosen global scalar action to an open subset. -/
@[stacks 01BH "global sections to an open"]
noncomputable abbrev globalSectionsToOpen
    (alpha : R →+* X.globalSectionsRing) (U : Opens X) :
    R →+* X.presheaf.obj (op U) :=
  (X.presheaf.map (topOpenRestriction (X := X) (op U))).hom.comp alpha

/-- Restricting a global scalar map to the top open recovers the original map. -/
@[stacks 01BH "global scalar map on the top open", simp]
theorem globalSectionsToOpen_top (alpha : R →+* X.globalSectionsRing) :
    globalSectionsToOpen alpha (⊤ : Opens X) = alpha := sorry

/-- Restriction from global sections to opens is compatible with further restriction. -/
theorem globalSectionsToOpen_map (alpha : R →+* X.globalSectionsRing)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    globalSectionsToOpen alpha V.unop =
      (X.presheaf.map f).hom.comp (globalSectionsToOpen alpha U.unop) := sorry

/-- The value on `U` obtained by restricting a global module section. -/
noncomputable abbrev moduleGlobalSectionsToOpenValue
    (G : X.Modules) (U : Opens X) (m : G.val.obj (op (⊤ : Opens X))) :
    G.val.obj (op U) :=
  G.val.map (topOpenRestriction (X := X) (op U)) m

/-- Restriction of a global module section is semilinear for the induced scalar map. -/
theorem moduleGlobalSectionsToOpen_smul
    (alpha : R →+* X.globalSectionsRing) (G : X.Modules) (U : Opens X)
    (r : R) (m : X.moduleGlobalSectionsRestriction alpha G) :
    moduleGlobalSectionsToOpenValue G U (r • m) =
      globalSectionsToOpen alpha U r •
        moduleGlobalSectionsToOpenValue G U m := sorry

/-- Restrict global module sections to an open subset, retaining the chosen global scalars. -/
noncomputable def moduleGlobalSectionsToOpen
    (alpha : R →+* X.globalSectionsRing) (G : X.Modules) (U : Opens X) :
    X.moduleGlobalSectionsRestriction alpha G ⟶
      (ModuleCat.restrictScalars (globalSectionsToOpen alpha U)).obj
        ((moduleSectionsEvaluationFunctor X U).obj G) :=
  (ModuleCat.semilinearMapAddEquiv (globalSectionsToOpen alpha U)
    (X.moduleGlobalSectionsRestriction alpha G)
    ((moduleSectionsEvaluationFunctor X U).obj G))
    { toFun := moduleGlobalSectionsToOpenValue G U
      map_add' := (G.val.map (topOpenRestriction (X := X) (op U))).hom.map_add
      map_smul' := moduleGlobalSectionsToOpen_smul alpha G U }

/-- Restriction of global module sections to an open is natural in the module sheaf. -/
theorem moduleGlobalSectionsToOpen_naturality
    (alpha : R →+* X.globalSectionsRing) (U : Opens X)
    {G H : X.Modules} (f : G ⟶ H) :
    (X.moduleGlobalSectionsRestrictionFunctor alpha).map f ≫
        moduleGlobalSectionsToOpen alpha H U =
      moduleGlobalSectionsToOpen alpha G U ≫
        (ModuleCat.restrictScalars (globalSectionsToOpen alpha U)).map
          ((moduleSectionsEvaluationFunctor X U).map f) := sorry

/-- Restriction from global sections to an open subset as a natural transformation. -/
@[stacks 01BH "global sections to an open natural transformation"]
noncomputable def moduleGlobalSectionsToOpenNatTrans
    (alpha : R →+* X.globalSectionsRing) (U : Opens X) :
    X.moduleGlobalSectionsRestrictionFunctor alpha ⟶
      moduleSectionsEvaluationFunctor X U ⋙
        ModuleCat.restrictScalars (globalSectionsToOpen alpha U) where
  app G := moduleGlobalSectionsToOpen alpha G U
  naturality _ _ f := moduleGlobalSectionsToOpen_naturality alpha U f

end AlgebraicGeometry.RingedSpace
