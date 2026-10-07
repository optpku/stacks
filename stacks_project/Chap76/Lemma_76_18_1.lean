module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Infinitesimal deformations of algebraic spaces

For a morphism of first-order thickenings of algebraic spaces whose map on the
closed subspaces is flat, flatness of the ambient map together with cartesianness
is equivalent to the canonical conormal comparison being an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

/-- Lemma 76.18.1: Let `S` be a scheme. Let `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a
morphism of first-order thickenings of algebraic spaces over `S`. Assume that
`f` is flat. Then `f'` is flat and `X = Y ×_{Y'} X'` if and only if the canonical
map `f^* C_{Y/Y'} ⟶ C_{X/X'}` is an isomorphism. -/
@[stacks 06BH]
theorem flat_ambient_and_isPullback_iff_conormalMap_isIso
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S} {iX : X ⟶ X'} {iY : Y ⟶ Y'}
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] {f : X ⟶ Y}
    {f' : X' ⟶ Y'} [Flat f] (sq : CommSq f iX iY f') :
    (Flat f' ∧ IsPullback f iX iY f') ↔ IsIso (Hom.Conormal.map sq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
