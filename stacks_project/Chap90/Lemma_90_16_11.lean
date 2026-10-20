/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over
import StacksCheckRecall

/-!
# Localizing the Rim-Schlessinger condition at a residue-fibre object

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS),
then so does its slice at any residue-fibre object, and that slice is a deformation
category.
-/

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 90.16.11 (1): if `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies (RS) and
`x` is an object of the residue fibre `p.Fiber (ArtinianLocalAlgCat.residue Λ k)`,
then the slice `Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` of Remark 90.6.4
also satisfies (RS). -/
@[stacks 06JC] #check (CategoryTheory.Functor.instHasRimSchlessinger_overForget :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)),
    Functor.HasRimSchlessinger (Over.forget (Functor.Fiber.fiberInclusion.obj x) ⋙ p))

/- Lemma 90.16.11 (2): in particular, the slice
`Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` is a deformation category. -/
@[stacks 06JC] #check (CategoryTheory.Functor.instIsDeformationCategory_overForget :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)),
    Functor.IsDeformationCategory (Over.forget (Functor.Fiber.fiberInclusion.obj x) ⋙ p))
