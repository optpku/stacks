/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.TypeValued
import StacksCheckRecall

/-!
# Smooth morphisms of categories cofibered in sets

When categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` are cofibered
in sets, Stacks smoothness of the corresponding morphism is Schlessinger smoothness
of the associated functors.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/- Remark 90.8.4: when categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
are cofibered in sets, associated via `Functor.ofTypeValued` to functors
`F, G : ArtinianLocalAlgCat Λ k ⥤ Type v`, Stacks smoothness of
`CofiberedCategoryOver.Groupoids.toBasedFunctor (Functor.ofTypeValuedMap η)` is
equivalent to Schlessinger smoothness `NatTrans.IsSmooth η`. Equivalently, `η` is
smooth if and only if for every surjection `f : B ⟶ A` the comparison
`NatTrans.liftPair η f : F.obj B → F.obj A × G.obj B` is surjective onto pairs
`(x, y)` satisfying `η.app A x = G.map f y`. This is analogous to the
characterization in Remark 90.8.3 and to Schlessinger's Definition 2.2. -/
@[stacks 06HJ] #check (CategoryTheory.BasedFunctor.isSmooth_ofTypeValuedMap_iff :
  ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G),
    IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor (Functor.ofTypeValuedMap η)) ↔
      NatTrans.IsSmooth η)

/- Stacks smoothness of `ofTypeValuedMap η` is equivalent to the fibre-product
surjectivity of `NatTrans.liftPair η f` along every surjection `f : B ⟶ A`. -/
#check (CategoryTheory.BasedFunctor.isSmooth_ofTypeValuedMap_iff_liftPair :
  ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G),
    IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor (Functor.ofTypeValuedMap η)) ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ (x : F.obj A) (y : G.obj B), η.app A x = G.map f y →
          ∃ x' : F.obj B, NatTrans.liftPair η f x' = (x, y))

end CategoryTheory.BasedFunctor
