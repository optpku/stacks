/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RepresentableDescent
import StacksCheckRecall

/-!
# Lemma 81.4.3

A representable morphism of algebraic spaces that is surjective integral,
surjective proper, or surjective flat and locally of finite presentation
satisfies descent for Type-valued sheaves on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/- Lemma 81.4.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is representable by schemes and is either surjective and
integral, surjective and proper, or surjective and flat and locally of finite
presentation, then the functor from Type-valued sheaves on the small étale site
of `Y` to singleton descent data along `{f}` is an equivalence of categories. -/
@[stacks 0GFU] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [Surjective f]
      (h : IsIntegralHom f ∨ Proper f ∨ (Flat f ∧ LocallyOfFinitePresentation f)),
      (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence)

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
