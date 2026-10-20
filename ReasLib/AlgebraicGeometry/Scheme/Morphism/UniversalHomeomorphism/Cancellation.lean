/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Cancellation for universal homeomorphisms

Universal homeomorphisms satisfy both cancellation directions for composable scheme morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism

/-- If a composite and its left factor are universal homeomorphisms, then its right factor is a
universal homeomorphism. -/
theorem right_of_comp_left
    {X Y Z : Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z}
    (hcomp : AlgebraicGeometry.UniversalHomeomorphism (g ≫ h))
    (hg : AlgebraicGeometry.UniversalHomeomorphism g) :
    AlgebraicGeometry.UniversalHomeomorphism h := sorry

/-- If a composite and its right factor are universal homeomorphisms, then its left factor is a
universal homeomorphism. -/
theorem left_of_comp_right
    {X Y Z : Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z}
    (hcomp : AlgebraicGeometry.UniversalHomeomorphism (g ≫ h))
    (hh : AlgebraicGeometry.UniversalHomeomorphism h) :
    AlgebraicGeometry.UniversalHomeomorphism g := sorry

end AlgebraicGeometry.UniversalHomeomorphism
