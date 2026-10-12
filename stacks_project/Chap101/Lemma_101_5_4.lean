/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_5_4_Action
public import stacks_project.Chap101.Lemma_101_5_4_Comparison
import StacksCheckRecall

/-!
# Lemma 101.5.4

For a morphism of algebraic stacks and morphisms from an algebraic space, the
relative automorphism sheaf is a group algebraic space, it sits in a left-exact
sequence of groups, relative isomorphisms arise by cartesian pullback along a
2-morphism, and that relative isomorphism space is a pseudo-torsor for the
relative automorphism sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y) {Z : AlgebraicSpace S}

/- Lemma 101.5.4 (1): `Isom_{X/Y}(x2, x2)` is a group algebraic space over `Z`,
as the group object `asHomotopy f x2` in the homotopy category of
`SpacesOver Z.toGroupoids`. -/
@[stacks 0CPK]
#check AlgebraicGeometry.AlgebraicStack.RelativeIsom.instGrpObj_asHomotopy

/- Lemma 101.5.4 (2): there is a left-exact sequence of groups
`0 ⟶ Isom_{X/Y}(x2, x2) ⟶ Isom_X(x2, x2) ⟶ Isom_Y(f ∘ x2, f ∘ x2)`,
where the first nonzero map is `kernelι` and the second map is `toTarget`
equalized against `constOne`. -/
@[stacks 0CPK]
#check AlgebraicGeometry.AlgebraicStack.RelativeIsom.isomExactSequence

variable (x1 x2 : Z.toGroupoids ⟶ X) (α : x1 ≫ f ≅ x2 ≫ f)

/- Lemma 101.5.4 (3): the comparison `Isom_X(x1, x2) ⟶ Isom_Y(f ∘ x1, f ∘ x2)`
is `pairComparison f x1 x2`, and for any 2-morphism
`α : f ∘ x1 ⟶ f ∘ x2` the square with corners `relativeIsom f α`, `Z`,
`TwoFibreProduct.apex x1 x2`, and `TwoFibreProduct.apex (x1 ≫ f) (x2 ≫ f)`
and legs `relativeIsom.fst`, `relativeIsom.snd`, `pairComparison`, and
`diagonalAlpha` is a 2-fibre product. -/
@[stacks 0CPK]
#check (TwoFibreProduct.cone.isBilimit.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α) :
  (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α)).IsBilimit)

/- Lemma 101.5.4 (4): for any 2-morphism `α : f ∘ x1 ⟶ f ∘ x2`, the algebraic
space `Isom^α_{X/Y}(x1, x2)` is a pseudo-torsor for `Isom_{X/Y}(x2, x2)`
over `Z`. -/
@[stacks 0CPK]
#check AlgebraicGeometry.AlgebraicStack.RelativeIsom.instIsPseudoTorsor_action

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
