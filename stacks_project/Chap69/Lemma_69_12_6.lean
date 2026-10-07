module

public import stacks_project.Chap69.Lemma_69_12_6_Neighborhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.12.6 (1): a coherent module on a locally Noetherian algebraic space which vanishes
at a geometric stalk vanishes on some open neighbourhood of the image point. -/
@[stacks 07UF]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent.existsNeighborhood_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      (F : X.Modules) [F.IsCoherent] (xbar : GeometricPoint X)
      (_ : IsZero (stalkModuleCat xbar F)),
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      IsZero ((Modules.pullback X'.ι).obj F))

/- Lemma 69.12.6 (2): a morphism of coherent modules on a locally Noetherian algebraic space
which is injective at a geometric stalk is a monomorphism on some open neighbourhood. -/
@[stacks 07UF]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent.existsNeighborhood_mono_of_injective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (xbar : GeometricPoint X)
      (_ : Function.Injective (stalkModuleCatMap xbar φ).hom),
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      Mono ((Modules.pullback X'.ι).map φ))

/- Lemma 69.12.6 (3): a morphism of coherent modules on a locally Noetherian algebraic space
which is surjective at a geometric stalk is an epimorphism on some open neighbourhood. -/
@[stacks 07UF]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent.existsNeighborhood_epi_of_surjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (xbar : GeometricPoint X)
      (_ : Function.Surjective (stalkModuleCatMap xbar φ).hom),
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      Epi ((Modules.pullback X'.ι).map φ))

/- Lemma 69.12.6 (4): a morphism of coherent modules on a locally Noetherian algebraic space
which is bijective at a geometric stalk is an isomorphism on some open neighbourhood. -/
@[stacks 07UF]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent.existsNeighborhood_isIso_of_bijective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (xbar : GeometricPoint X)
      (_ : Function.Bijective (stalkModuleCatMap xbar φ).hom),
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      IsIso ((Modules.pullback X'.ι).map φ))
