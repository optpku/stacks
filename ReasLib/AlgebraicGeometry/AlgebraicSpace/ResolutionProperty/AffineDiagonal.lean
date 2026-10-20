/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Affine diagonal from the resolution property of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact and absolutely quasi-separated algebraic space with the resolution
property has affine diagonal over the terminal scheme. -/
theorem affineDiagonal_of_hasResolutionProperty {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : SheafOfModules.HasResolutionProperty (structureSheaf X)) :
    (MorphismProperty.over (@IsAffineHom)).presheaf (diag (extendBaseTerminal X)) := sorry

end AlgebraicGeometry.AlgebraicSpace
