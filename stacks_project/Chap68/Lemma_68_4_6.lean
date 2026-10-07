module

public import stacks_project.Chap68.Lemma_68_4_6_Fibre

/-!
# Universally bounded étale fibres of an algebraic space

Existence of an étale scheme covering with universally bounded fibres is
equivalent to the affine étale universally-bounded-fibre test.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
The following are equivalent: there exist schemes `U i` and étale morphisms
`φ i : ofOver (U i) ⟶ X` such that `∐ φ i : ∐ U i ⟶ X` is surjective and each
`U i ⟶ X` has universally bounded fibres; and for every affine scheme `U` and
étale morphism `φ : ofOver U ⟶ X` the fibres of `U ⟶ X` are universally
bounded. -/
@[stacks 03JT]
theorem existsEtaleCoverUniversallyBoundedFibres_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    existsEtaleCoverUniversallyBoundedFibres X ↔
      forallAffineEtaleUniversallyBoundedFibres X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
