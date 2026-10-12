/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified

/-!
# Existence of universal first-order thickenings

A formally unramified morphism of algebraic spaces over a scheme admits a
universal first-order thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- Lemma 76.15.4: Let `S` be a scheme. Let `h : Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `S`. There exists a universal first-order
thickening of `Z` over `X`, i.e. algebraic spaces and morphisms
`i : Z ⟶ Z'` and `f : Z' ⟶ X` with `i ≫ f = h` such that
`IsUniversalFirstOrder i f`. -/
@[stacks 0606]
theorem exists_of_formallyUnramified {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (f : Z' ⟶ X),
      i ≫ f = h ∧ IsUniversalFirstOrder i f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
