/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Koszul.Locus
import StacksCheckRecall

/-!
# Koszul locus of a morphism of algebraic spaces over a triangle

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with both
structure maps flat and locally of finite presentation, the Koszul locus of
`f` is an open subspace of `X`, and formation of this open commutes with
arbitrary base change of the triangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.48.11 (1): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z`
with `f ≫ q = p`. Assume that both `p` and `q` are flat and locally of finite
presentation. Then `(koszulLocus f).pointsSet` is the set of points of
`Points X` at which `f` is Koszul. -/
@[stacks 06CA] #check
  (AlgebraicGeometry.AlgebraicSpace.koszulLocus_pointsSet_eq_of_over :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (h_over : f ≫ q = p) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q],
    (koszulLocus f).pointsSet = {x | KoszulAt f x})

/- Lemma 76.48.11 (2): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z`
with `f ≫ q = p`. Assume that both `p` and `q` are flat and locally of finite
presentation. For any morphism `g : Z' ⟶ Z` of algebraic spaces over `S`, if
`f' : X' ⟶ Y'` is the base change of `f` by `g`, then
`(koszulLocus f').pointsSet` is the inverse image of
`(koszulLocus f).pointsSet` under the projection `X' ⟶ X`. -/
@[stacks 06CA] #check
  (AlgebraicGeometry.AlgebraicSpace.koszulLocus_pointsSet_eq_preimage_of_baseChange :
    ∀ {S : Scheme.{u}}
    {X Y Z X' Y' Z' : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (f' : X' ⟶ Y') (p' : X' ⟶ Z') (q' : Y' ⟶ Z') (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (g : Z' ⟶ Z) (h_over : f ≫ q = p) (h_over' : f' ≫ q' = p')
    (sq : CommSq f' gX gY f) (hX : IsPullback gX p' p g)
    (hY : IsPullback gY q' q g) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q],
    (koszulLocus f').pointsSet = Points.map gX ⁻¹' (koszulLocus f).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
