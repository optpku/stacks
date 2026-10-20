/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

/-!
# Universal property of zero schemes on algebraic spaces

A morphism of algebraic spaces over `S` pulls a section of an invertible module
back to zero if and only if it factors through the zero scheme of that section.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullback of a section vanishes if and only if the zero ideal vanishes along
the morphism. -/
theorem pullbackSections_eq_zero_iff_vanishes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (f : Y ⟶ X) :
    Modules.sectionsPullback f L s = 0 ↔ vanishes f (zeroIdealSubobject L s) :=
  sorry

/-- Pullback of a section vanishes if and only if the morphism factors through the
zero scheme of that section. -/
theorem pullbackSections_eq_zero_iff_exists_factorization_zeroScheme
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (f : Y ⟶ X) :
    Modules.sectionsPullback f L s = 0 ↔
      ∃ g : Y ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = f :=
  sorry

/-- A section of an invertible module vanishes after pullback along
the closed immersion of its zero scheme. -/
theorem zeroSchemeι_pullbackSections_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    Modules.sectionsPullback (zeroSchemeι L s) L s = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
