/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.CategoryTheory.Cofibered.Grothendieck

/-!
# Smoothness of morphisms induced by set-valued functors

Smoothness of a morphism between the cofibered categories associated to set-valued
functors on Artinian local algebras is equivalent to the Schlessinger lifting
property of the underlying natural transformation.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- Smoothness of the morphism between the cofibered categories associated to
set-valued functors on `ArtinianLocalAlgCat Λ k` is equivalent to Schlessinger
smoothness of the underlying natural transformation. -/
@[stacks 06HJ]
theorem isSmooth_ofTypeValuedMap_iff {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G) :
    IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor (Functor.ofTypeValuedMap η)) ↔
      NatTrans.IsSmooth η :=
  sorry

/-- Stacks smoothness of `ofTypeValuedMap η` is equivalent to the fibre-product
surjectivity of `NatTrans.liftPair η f` along every surjection `f : B ⟶ A`. -/
theorem isSmooth_ofTypeValuedMap_iff_liftPair
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G) :
    IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor (Functor.ofTypeValuedMap η)) ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ (x : F.obj A) (y : G.obj B), η.app A x = G.map f y →
          ∃ x' : F.obj B, NatTrans.liftPair η f x' = (x, y) :=
  sorry

end CategoryTheory.BasedFunctor
