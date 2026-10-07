module

public import stacks_project.Chap68.Lemma_68_4_7_Cover

/-!
# Quasi-compact self-fibre étale coverings of algebraic spaces

Existence of a Zariski covering by quasi-compact surjective étale scheme charts
is equivalent to an étale family of schemes with quasi-compact self-fibre
projections whose coproduct is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.7: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
The following are equivalent: there exists a Zariski covering `X = ⋃ X i` and
for each `i` a scheme `U i` and a quasi-compact surjective étale morphism
`U i ⟶ X i`; and there exist schemes `U i` and étale morphisms `U i ⟶ X`
such that the projections `U i ×_X U i ⟶ U i` are quasi-compact and
`∐ U i ⟶ X` is surjective. -/
@[stacks 03IH]
theorem existsZariskiCoverQuasiCompactSurjectiveEtale_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    existsZariskiCoverQuasiCompactSurjectiveEtale X ↔
      existsEtaleCoverQuasiCompactSelfFibre X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
