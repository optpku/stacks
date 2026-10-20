/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Composition of pullback maps on global sections

This leaf provides the canonical comparison from global sections after two
scheme-module pullbacks to global sections after their composite.  It keeps
the pseudofunctorial pullback comparison explicit, rather than hiding it in
applications that work with inverse systems of schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The map on global sections obtained by pulling back first along `g`, then
along `f`, and comparing the resulting module with pullback along `f ≫ g`. -/
noncomputable def globalSectionsPullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    globalSections ((pullback g).obj F) ⟶
      globalSections ((pullback (f ≫ g)).obj F) :=
  globalSectionsPullback f ((pullback g).obj F) ≫
    globalSectionsMap ((pullbackComp f g).hom.app F)

/-- Pulling back global sections through `g` and then `f` agrees with the
global-sections pullback map for `f ≫ g`. -/
theorem globalSectionsPullback_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    globalSectionsPullback g F ≫ globalSectionsPullbackComp f g F =
      globalSectionsPullback (f ≫ g) F := sorry

end AlgebraicGeometry.Scheme.Modules
