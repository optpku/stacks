module

public import stacks_project.Chap67.Lemma_67_8_8_Local
import StacksCheckRecall

@[expose] public section

/- Lemma 67.8.8 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff for every scheme `Z` and morphism `Z ⟶ Y` the
base-change projection `Z ×_Y X ⟶ Z` is quasi-compact. -/
@[stacks 03KG] #check AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_forall_scheme

/- Lemma 67.8.8 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff for every affine scheme `Z` and morphism `Z ⟶ Y` the
algebraic space `Z ×_Y X` is quasi-compact. -/
@[stacks 03KG] #check AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_forall_affine

/- Lemma 67.8.8 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that `V ×_Y X ⟶ V` is quasi-compact. -/
@[stacks 03KG] #check AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_etale_scheme

/- Lemma 67.8.8 (4): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a surjective étale morphism `Y' ⟶ Y` of
algebraic spaces such that `Y' ×_Y X ⟶ Y'` is quasi-compact. -/
@[stacks 03KG] #check AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_etale

/- Lemma 67.8.8 (5): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a Zariski covering `Y = ⋃ Yᵢ` such that
each inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` is quasi-compact. -/
@[stacks 03KG] #check AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_zariskiCover
