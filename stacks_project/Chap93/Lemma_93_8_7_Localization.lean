/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization
import StacksCheckRecall

/-!
# Localization of ring deformation categories

Localization at a multiplicative subset induces a functor on flat deformations and
preserves their Artinian local bases.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]

/- Lemma 93.8.7 (Localization)
A multiplicative subset of a residue-field algebra induces the localization functor
on its deformation category.
-/
@[stacks 0DYS] #check (FlatAlgebraCat.localizationFunctor :
  ∀ (S : Submonoid P),
    FlatAlgebraCat.deformationCategory Λ k P ⥤
      FlatAlgebraCat.deformationCategory Λ k (Localization S))

#check (FlatAlgebraCat.localizationBasedFunctor Λ k :
  ∀ (S : Submonoid P),
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)) ⋙
          (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget
            (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k (Localization S))) ⋙
          (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)))
