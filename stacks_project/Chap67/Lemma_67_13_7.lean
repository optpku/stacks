module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula

/-!
# Lemma 67.13.7

For a closed immersion of algebraic spaces, the canonical projection-formula map
of étale modules along the associated morphism of ringed topoi is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.13.7: if `i : Z ⟶ X` is a closed immersion of algebraic spaces over a scheme `S`,
`A` is a sheaf of rings on `X_étale`, `B` is a sheaf of rings on `Z_étale`, and
`φ : A ⟶ i_small,* B` presents a morphism of ringed topoi
`f : (Sh(Z_étale), B) ⟶ (Sh(X_étale), A)`, then for every sheaf of `A`-modules `F` and sheaf of
`B`-modules `G` the canonical map `F ⊗_A f_* G ⟶ f_*(f^* F ⊗_B G)` is an isomorphism. -/
@[stacks 04G0, instance]
instance IsClosedImmersion.isIso_projectionFormula
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    (φ : (etaleRingedSite X A).structureSheaf ⟶
      (ringPushforward i).obj (etaleRingedSite Z B).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite Z B).structureSheaf) :
    IsIso (projectionFormula i φ F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
