/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions

/-!
# Flatness of closed subschemes in sufficiently large dimensions

Dimensional flatness of a closed subscheme is expressed by dimensional flatness
of its structure sheaf pushed forward to the ambient scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The closed subscheme `Z ⊂ X` is flat over `S` in dimensions `≥ r` when the
pushed-forward structure sheaf `(Z ⟶ X)_* O_Z` is flat over `S` in dimensions
`≥ r`. -/
def closedSubschemeFlatOverInDimensionsGE {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : X.IdealSheafData) (r : ℕ) : Prop :=
  Modules.flatOverInDimensionsGE (closedSubschemeStructureSheafOn Z) f r

/-- Flatness of `Z` over `S` in dimensions `≥ r` is the module-theoretic
condition on `(Z ⟶ X)_* O_Z`. -/
theorem closedSubschemeFlatOverInDimensionsGE_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ) :
    f.closedSubschemeFlatOverInDimensionsGE Z r ↔
      Modules.flatOverInDimensionsGE (closedSubschemeStructureSheafOn Z) f r := Iff.rfl

/-- If `Z ⟶ S` is flat, then `Z` is flat over `S` in dimensions `≥ r`. -/
theorem closedSubschemeFlatOverInDimensionsGE_of_flat {X S : Scheme.{u}}
    (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ)
    (hflat : Flat (Z.subschemeι ≫ f)) :
    f.closedSubschemeFlatOverInDimensionsGE Z r := sorry

end AlgebraicGeometry.Scheme.Hom
