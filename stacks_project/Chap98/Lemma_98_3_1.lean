/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
import StacksCheckRecall

/-!
# Predeformation categories from categories fibred in groupoids over schemes

The functor `p : ℱ_{X, k, x0} ⟶ ArtinianLocalAlgCat Λ k` constructed in
98.3.0.2 is a predeformation category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 98.3.1: the functor `p : ℱ_{X, k, x0} ⟶ ArtinianLocalAlgCat Λ k`
defined above is a predeformation category. -/
@[stacks 07T5] #check
  (AlgebraicGeometry.GroupoidsOver.Predeformation.instIsPredeformationCategory_predeformationFunctor :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
      [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : X.p.Fiber (Over.mk kToS)),
      CategoryTheory.Functor.IsPredeformationCategory
        (AlgebraicGeometry.GroupoidsOver.Predeformation.predeformationFunctor
          X openImmersion kToS h_factor x0))
