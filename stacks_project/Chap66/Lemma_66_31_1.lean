module

public import stacks_project.Chap66.Lemma_66_31_1_LocallyProjective

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 66.31.1: let `S` be a scheme, let `X` be an algebraic space over `S`, and let `F`
be a quasi-coherent `𝒪_X`-module. The following are equivalent: there exists a scheme `U` and
a surjective étale morphism `U ⟶ X` such that the restriction of `F` to `U` is locally
projective on `U`; for every scheme `U` and every étale morphism `U ⟶ X`, the restriction of
`F` to `U` is locally projective on `U`. -/
@[stacks 060Q]
theorem existsSurjectiveEtale_iff_forallEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] : existsSurjectiveEtale F ↔ forallEtale F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
