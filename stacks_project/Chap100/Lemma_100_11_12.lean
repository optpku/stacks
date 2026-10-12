/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe

/-!
# Residual gerbes from monomorphisms of singleton stacks

A monomorphism from a reduced, locally Noetherian singleton algebraic stack
whose image on points is a single point `x` produces the residual gerbe of
the target at `x`, and is equivalent to it over the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Lemma 100.11.12 (1): Let `X` be an algebraic stack. Let `x ∈ |X|`. Let `Z`
be an algebraic stack satisfying the equivalent conditions of Lemma 100.11.3
and let `Z ⟶ X` be a monomorphism such that the image of `|Z| ⟶ |X|` is `x`.
Then the residual gerbe of `X` at `x` exists. -/
@[stacks 06MX]
theorem exists_of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [IsReduced Z] [IsLocallyNoetherian Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] {x : Points X}
    (hx : Set.range (Points.map f) = {x}) :
    HasResidualGerbe X x :=
  sorry

/-- Lemma 100.11.12 (2): Let `X` be an algebraic stack. Let `x ∈ |X|`. Let `Z`
be an algebraic stack satisfying the equivalent conditions of Lemma 100.11.3
and let `Z ⟶ X` be a monomorphism such that the image of `|Z| ⟶ |X|` is `x`.
If the residual gerbe of `X` at `x` exists, then `Z ⟶ X` factors as
`Z ⟶ residualGerbe X x ⟶ X` where the first arrow is an equivalence. -/
@[stacks 06MX]
theorem factors_of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [IsReduced Z] [IsLocallyNoetherian Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] {x : Points X}
    (hx : Set.range (Points.map f) = {x}) [HasResidualGerbe X x] :
    ∃ g : Z ⟶ residualGerbe X x,
      (toBasedFunctor g).IsEquivalence ∧
        Nonempty (g ≫ residualGerbeι X x ≅ f) :=
  sorry

/-- A monomorphism from a reduced, locally Noetherian singleton algebraic stack
whose image on points is `{x}` is a residual gerbe at `x`. -/
theorem of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [IsReduced Z] [IsLocallyNoetherian Z]
    [Subsingleton (Points Z)] (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    {x : Points X} (hx : Set.range (Points.map f) = {x}) :
    IsResidualGerbe f x :=
  sorry

/-- Any two residual gerbes of an algebraic stack at the same point are
equivalent over that stack. -/
theorem unique {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x] :
    ∃ g : Z ⟶ Zx, (toBasedFunctor g).IsEquivalence ∧ Nonempty (g ≫ ι ≅ f) :=
  sorry

/-- Comparison 1-morphisms between residual gerbes at the same point are unique
up to 2-isomorphism. -/
theorem unique_lift {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x]
    (g g' : Z ⟶ Zx) (hg : Nonempty (g ≫ ι ≅ f))
    (hg' : Nonempty (g' ≫ ι ≅ f)) :
    Nonempty (g ≅ g') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
