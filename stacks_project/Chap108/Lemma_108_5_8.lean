module

public import stacks_project.Chap108.Lemma_108_5_8_Map

/-!
# Lemma 108.5.8

A surjection of quasi-coherent modules on a separated finite-presentation
algebraic space over `B` induces a closed immersion of Grothendieck Quot
functors by precomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.5.8: If `f : X ⟶ B` is separated and of finite presentation and
`φ : F ⟶ G` is a surjection of quasi-coherent `𝒪_X`-modules, then the canonical
comparison `precompHom f φ : quot f G ⟶ quot f F` is a closed immersion of
functors of schemes over `B`. -/
@[stacks 0DP5]
theorem isClosedImmersion_precompHom (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) [Epi φ] :
    IsClosedImmersionOnSchemesOver (precompHom f φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
