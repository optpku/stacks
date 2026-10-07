module

public import stacks_project.Chap68.Lemma_68_4_2_Fibre

/-!
# Finite étale fibres over a point of an algebraic space

Existence of an étale scheme covering with finite fibres over a point is
equivalent to the affine étale finite-fibre test.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. The following are equivalent: there exists a family of
schemes `U i` and étale morphisms `φ i : ofOver (U i) ⟶ X` such that
`∐ φ i : ∐ U i ⟶ X` is surjective, and such that for each `i` the fibre of
`|U i| → |X|` over `x` is finite; and for every affine scheme `U` and étale
morphism `φ : ofOver U ⟶ X` the fibre of `|U| → |X|` over `x` is finite. -/
@[stacks 03JS]
theorem existsEtaleCoverFiniteFibre_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    existsEtaleCoverFiniteFibre X x ↔ forallAffineEtaleFiniteFibre X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
