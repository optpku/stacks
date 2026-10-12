/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

/-!
# Predeformation categories from residue-fibre slices

The slice over a residue-fibre object of a category cofibered in groupoids is
again a predeformation category under its forgetful projection.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Slicing a category cofibered in groupoids at a residue-fibre object produces a
predeformation category through the forgetful functor from the resulting over category. -/
instance instIsPredeformationCategory_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    IsPredeformationCategory (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
