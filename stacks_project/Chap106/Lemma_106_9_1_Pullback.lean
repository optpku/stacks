/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap71.Lemma_71_19_4_CommonRefinement
public import stacks_project.Chap106.Definition_106_12_1_Moduli

/-!
# First projection of stack–space pullbacks

The first projection of the chosen 2-fibre product of a morphism from an
algebraic stack to an algebraic space, and the predicate that a closed
substack of a base change agrees with the original stack over an open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The first projection `Y' ×_Y X ⟶ X` of a morphism `f : X ⟶ Y.toGroupoids`
from an algebraic stack to an algebraic space, along a morphism `h : Y' ⟶ Y`
of algebraic spaces. -/
abbrev pullbackFst {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) : pullback f h ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f (AlgebraicSpace.toGroupoids.map h)

/-- `pullbackFst f h` is the first projection of the chosen 2-fibre product of
`f` against `AlgebraicSpace.toGroupoids.map h`. -/
theorem pullbackFst_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) :
    pullbackFst f h =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map h) :=
  sorry

namespace ClosedSubstack

/-- A closed substack `X' ⊂ X_{Y'}` restricts to the open fibre `X_{V'}` when
the projection `X' ×_{X_{Y'}} X_{V'} ⟶ X_{V'}` is an isomorphism. Here `V'` is
`V.inverseImage b` and the open fibre inclusion is
`pullbackFst (pullbackSnd f b) (V.inverseImage b).ι`. -/
def restrictsToOpen {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Y' : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) (b : Y' ⟶ Y)
    (V : AlgebraicSpace.OpenSubspace Y) (X' : ClosedSubstack (pullback f b)) :
    Prop :=
  IsIso
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} X'.ι
      (pullbackFst (pullbackSnd f b) (V.inverseImage b).ι))

/-- Restricting to the open fibre is the assertion that the 2-fibre-product
projection against the open fibre inclusion is an isomorphism. -/
theorem restrictsToOpen_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y Y' : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (b : Y' ⟶ Y) (V : AlgebraicSpace.OpenSubspace Y)
    (X' : ClosedSubstack (pullback f b)) :
    restrictsToOpen f b V X' ↔
      IsIso
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} X'.ι
          (pullbackFst (pullbackSnd f b) (V.inverseImage b).ι)) :=
  sorry

/-- If a closed substack restricts to the open fibre, the corresponding
2-fibre-product projection is an isomorphism. -/
theorem restrictsToOpen_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y Y' : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (b : Y' ⟶ Y) (V : AlgebraicSpace.OpenSubspace Y)
    (X' : ClosedSubstack (pullback f b)) (h : restrictsToOpen f b V X') :
    IsIso
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} X'.ι
        (pullbackFst (pullbackSnd f b) (V.inverseImage b).ι)) :=
  sorry

end ClosedSubstack

end AlgebraicGeometry.AlgebraicStack
