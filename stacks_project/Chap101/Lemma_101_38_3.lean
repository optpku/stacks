/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_38_2_SchemeTheoreticImage

/-!
# Existence of scheme-theoretic images of morphisms of algebraic stacks

Every morphism of algebraic stacks has a scheme-theoretic image: a least
strictly full closed substack of the target through which it factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.38.3: Let `f : 𝒴 ⟶ 𝒳` be a morphism of algebraic stacks.
Then the scheme-theoretic image of `f` exists. -/
@[stacks 0CPU]
theorem hasSchemeTheoreticImage {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSchemeTheoreticImage f :=
  sorry

/-- There exist a closed substack `Z` of `Y` and a 1-morphism `toImage`
such that `(f, toImage, Z.ι)` is a scheme-theoretic image factorization. -/
theorem exists_schemeTheoreticImage {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ∃ (Z : ClosedSubstack Y) (toImage : X ⟶ Z.Y),
      IsSchemeTheoreticImage f toImage Z.ι :=
  sorry

/-- There exists a least closed substack of `Y` through which `f` factors:
any other such closed substack admits a comparison over `Y` up to
2-isomorphism. -/
theorem exists_least_closedSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ∃ Z : ClosedSubstack Y,
      factorsThrough f Z ∧
        ∀ Z' : ClosedSubstack Y, factorsThrough f Z' →
          ∃ k : Z.Y ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ Z.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
