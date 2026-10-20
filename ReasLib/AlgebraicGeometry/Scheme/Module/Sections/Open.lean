/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Restricting global sections to an open subscheme

This leaf owns the map from global sections of a scheme module to global
sections of its restriction to an open subscheme.  The implementation makes
the comparison between open restriction and module pullback explicit.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Restriction of global sections of `F` to the open subscheme associated to
`U`. -/
noncomputable def globalSectionsRestrict (U : X.Opens) (F : X.Modules) :
    globalSections F ⟶ globalSections ((restrictFunctor U.ι).obj F) :=
  globalSectionsPullback U.ι F ≫
    globalSectionsMap ((restrictFunctorIsoPullback U.ι).inv.app F)

/-- Restriction of global sections to an open subscheme is natural in the
module sheaf. -/
theorem globalSectionsRestrict_naturality
    (U : X.Opens) {F G : X.Modules} (φ : F ⟶ G) :
    globalSectionsMap φ ≫ globalSectionsRestrict U G =
      globalSectionsRestrict U F ≫ globalSectionsMap ((restrictFunctor U.ι).map φ) := sorry

end AlgebraicGeometry.Scheme.Modules
