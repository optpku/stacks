/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Localization
import StacksCheckRecall

/-!
# Localizing Schlessinger's conditions at a residue-fibre object

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (S1)
or (S2), then so does its slice at any residue-fibre object.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Functor

/- Lemma 90.10.6: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (S1) or (S2), then its slice at an object of the residue fibre
also satisfies the corresponding condition. -/
@[stacks 06SQ] #check
  (CategoryTheory.Functor.instHasSchlessingerS1_overForget :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] {F : Type v} [Category.{w} F]
      (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      [HasSchlessingerS1 p]
      (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)),
      HasSchlessingerS1 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p))

/- Lemma 90.10.6 (2): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (S2), then its slice at an object of the residue fibre also
satisfies (S2). -/
@[stacks 06SQ] #check
  (CategoryTheory.Functor.instHasSchlessingerS2_overForget :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] {F : Type v} [Category.{w} F]
      (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      [HasSchlessingerS2 p]
      (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)),
      HasSchlessingerS2 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p))

end CategoryTheory.Functor
