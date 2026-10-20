module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Locality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 67.8.8 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff for every scheme `Z` and morphism `Z ⟶ Y` the
base-change projection `Z ×_Y X ⟶ Z` is quasi-compact. -/
@[stacks 03KG] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_forall_scheme :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact f ↔
        ∀ (Z : CategoryTheory.Over S)
          (g : AlgebraicGeometry.AlgebraicSpace.ofOver Z ⟶ Y),
          AlgebraicGeometry.AlgebraicSpace.QuasiCompact
            (CategoryTheory.Limits.pullback.snd f g))

/- Lemma 67.8.8 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff for every affine scheme `Z` and morphism `Z ⟶ Y` the
algebraic space `Z ×_Y X` is quasi-compact. -/
@[stacks 03KG] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_forall_affine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact f ↔
        ∀ (Z : CategoryTheory.Over S) [AlgebraicGeometry.IsAffine Z.left]
          (g : AlgebraicGeometry.AlgebraicSpace.ofOver Z ⟶ Y),
          AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact
            (CategoryTheory.Limits.pullback f g))

/- Lemma 67.8.8 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that `V ×_Y X ⟶ V` is quasi-compact. -/
@[stacks 03KG] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_etale_scheme :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact f ↔
        ∃ (V : CategoryTheory.Over S)
          (g : AlgebraicGeometry.AlgebraicSpace.ofOver V ⟶ Y),
          AlgebraicGeometry.AlgebraicSpace.Etale g ∧
            AlgebraicGeometry.AlgebraicSpace.Surjective g ∧
              AlgebraicGeometry.AlgebraicSpace.QuasiCompact
                (CategoryTheory.Limits.pullback.snd f g))

/- Lemma 67.8.8 (4): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a surjective étale morphism `Y' ⟶ Y` of
algebraic spaces such that `Y' ×_Y X ⟶ Y'` is quasi-compact. -/
@[stacks 03KG] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_etale :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact f ↔
        ∃ (Y' : AlgebraicGeometry.AlgebraicSpace S)
          (g : Y' ⟶ Y),
          AlgebraicGeometry.AlgebraicSpace.Etale g ∧
            AlgebraicGeometry.AlgebraicSpace.Surjective g ∧
              AlgebraicGeometry.AlgebraicSpace.QuasiCompact
                (CategoryTheory.Limits.pullback.snd f g))

/- Lemma 67.8.8 (5): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-compact iff there exists a Zariski covering `Y = ⋃ Yᵢ` such that
each inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` is quasi-compact. -/
@[stacks 03KG] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.iff_exists_zariskiCover :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact f ↔
        ∃ (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, u} Y),
          ∀ i, AlgebraicGeometry.AlgebraicSpace.QuasiCompact
            (CategoryTheory.Limits.pullback.snd f (𝒰.f i)))
