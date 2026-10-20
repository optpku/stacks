/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.Descent

/-!
# Descent of representable morphisms having a morphism property

A property `P` as in Definition 94.10.1 descends along an fppf-locally
essentially surjective 1-morphism of groupoid fibrations over `(Sch/S)_fppf`,
for 1-morphisms that are representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.Groupoids.Hom

/- Lemma 94.10.7: let `S` be a scheme in `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Definition 94.10.1. Let `f : X ⟶ Y` be a
1-morphism representable by algebraic spaces, and let `g : Z ⟶ Y` be any
1-morphism. In the 2-fibre-product square of `(g, f)`, the base change is
`f' := TwoFibreProduct.fst g f : Z ×_Y X ⟶ Z`. Assume `g` is locally
essentially surjective on `Scheme.fppfTopology.over S`: equivalently, for
every `U : Over S` and `x : Y.p.Fiber U` there is an fppf covering of `U`
along which the cleavage reindexing of `x` lies in the essential image of
`fiberFunctor g` (`LocallyEssentiallySurjective.iff_forall_cover` and
`EssentialImage.HasPreimage`). If `f'` has `P`, then `f` has `P`. -/
@[stacks 045D] #check (AlgebraicGeometry.Groupoids.Hom.has.of_pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : LocallyEssentiallySurjective (Scheme.fppfTopology.over S) g)
    (hf' : has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)),
    has P f)
