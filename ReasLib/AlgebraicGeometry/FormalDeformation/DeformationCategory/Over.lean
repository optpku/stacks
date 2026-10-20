/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# Deformation categories from residue-fibre slices

The Rim-Schlessinger condition is preserved by slicing at a residue-fibre object,
and the resulting slice is a deformation category.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Slicing a functor satisfying the Rim-Schlessinger condition at a residue-fibre
object preserves the Rim-Schlessinger condition under the forgetful projection. -/
instance instHasRimSchlessinger_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasRimSchlessinger (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

/-- The slice at a residue-fibre object of a functor satisfying the Rim-Schlessinger
condition is a deformation category under its forgetful projection. -/
instance instIsDeformationCategory_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    IsDeformationCategory (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
