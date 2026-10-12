/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_38_10_SourceLocus

/-!
# Unramified locus of a locally finite-type morphism of algebraic spaces

A commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with `X ⟶ Z`
locally of finite type has a canonical open subspace of the source consisting
of the points at which the map to `Y` is unramified, and formation of this open
commutes with arbitrary base change of the triangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.38.10 (1): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that
`X ⟶ Z` is locally of finite type. Then there is an open subspace
`Unramified.sourceLocus f ⊂ X` such that `(Unramified.sourceLocus f).pointsSet`
is the set of points of `Points X` at which `f` is unramified. -/
@[stacks 05W2]
theorem unramified_sourceLocus_pointsSet {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] :
    (Unramified.sourceLocus f).pointsSet = {x | UnramifiedAt f x} :=
  sorry

/-- Lemma 67.38.10 (2): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that
`X ⟶ Z` is locally of finite type. For any morphism `g : Z' ⟶ Z` of algebraic
spaces over `S`, if `f'` is the base change of `f` by `g`, then
`(Unramified.sourceLocus f').pointsSet` is the inverse image of
`(Unramified.sourceLocus f).pointsSet` under the projection `X' ⟶ X`. -/
@[stacks 05W2]
theorem unramified_sourceLocus_eq_preimage_of_over_baseChange
    {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] :
    (Unramified.sourceLocus (Unramified.overBaseChange f q g)).pointsSet =
      Points.map (pullback.fst (f ≫ q) g) ⁻¹'
        (Unramified.sourceLocus f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
