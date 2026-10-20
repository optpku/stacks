/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Composition

/-!
# Pulling back sections of scheme modules

This file provides transport of global sections through the monoidal comparison
for pullback and around cartesian squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pull back a section of a tensor product and transport it through the
canonical monoidal comparison for scheme-module pullback. -/
noncomputable def pullbackTensorSection
    (f : X ⟶ Y) {M N : Y.Modules} (s : (M ⊗ N).sections) :
    ((pullback f).obj M ⊗ (pullback f).obj N).sections :=
  SheafOfModules.sectionsMap (pullbackTensorIso f M N).hom
    (sectionsPullback f (M ⊗ N) s)

/-- The pullback tensor section is obtained by the section pullback followed by
the canonical tensor comparison. -/
theorem pullbackTensorSection_def
    (f : X ⟶ Y) {M N : Y.Modules} (s : (M ⊗ N).sections) :
    pullbackTensorSection f s =
      SheafOfModules.sectionsMap (pullbackTensorIso f M N).hom
        (sectionsPullback f (M ⊗ N) s) := sorry

/-- The canonical comparison between the two iterated pullbacks around a
commutative cartesian square. -/
noncomputable def pullbackSquareIso
    {X' Y' : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (M : Y.Modules) :
    (pullback a).obj ((pullback f).obj M) ≅
      (pullback b).obj ((pullback g).obj M) :=
  (pullbackComp a f).app M ≪≫
    (pullbackCongr sq.w).app M ≪≫
      ((pullbackComp b g).app M).symm

/-- Pull a section across the top map of a cartesian square and transport it
through `pullbackSquareIso`. -/
noncomputable def pullbackSectionAlongSquare
    {X' Y' : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g)
    (M : Y.Modules) (s : ((pullback f).obj M).sections) :
    ((pullback b).obj ((pullback g).obj M)).sections :=
  SheafOfModules.sectionsMap (pullbackSquareIso sq M).hom
    (sectionsPullback a ((pullback f).obj M) s)

/-- The section transported around a cartesian square uses the canonical
comparison of the two iterated pullbacks. -/
theorem pullbackSectionAlongSquare_def
    {X' Y' : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g)
    (M : Y.Modules) (s : ((pullback f).obj M).sections) :
    pullbackSectionAlongSquare sq M s =
      SheafOfModules.sectionsMap (pullbackSquareIso sq M).hom
        (sectionsPullback a ((pullback f).obj M) s) := sorry

end AlgebraicGeometry.Scheme.Modules
