module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Neighborhood properties of coherent modules on algebraic spaces

On a locally Noetherian algebraic space, vanishing of a coherent module at a
geometric stalk, and injectivity, surjectivity, or bijectivity of a morphism of
coherent modules at that stalk, persist after restriction to an open subspace
neighbourhood of the image point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent

/-- A coherent module sheaf with vanishing geometric stalk at `xbar` vanishes on some open
subspace neighbourhood of `xbar.image`. -/
theorem existsNeighborhood_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (xbar : GeometricPoint X) (hF : IsZero (stalkModuleCat xbar F)) :
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      IsZero ((pullback X'.ι).obj F) := sorry

/-- A morphism of coherent modules that is injective at a geometric stalk is a monomorphism
after restriction to some open subspace neighbourhood of the image point. -/
theorem existsNeighborhood_mono_of_injective {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (xbar : GeometricPoint X)
    (hφ : Function.Injective (stalkModuleCatMap xbar φ).hom) :
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      Mono ((pullback X'.ι).map φ) := sorry

/-- A morphism of coherent modules that is surjective at a geometric stalk is an epimorphism
after restriction to some open subspace neighbourhood of the image point. -/
theorem existsNeighborhood_epi_of_surjective {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (xbar : GeometricPoint X)
    (hφ : Function.Surjective (stalkModuleCatMap xbar φ).hom) :
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      Epi ((pullback X'.ι).map φ) := sorry

/-- A morphism of coherent modules that is bijective at a geometric stalk is an isomorphism
after restriction to some open subspace neighbourhood of the image point. -/
theorem existsNeighborhood_isIso_of_bijective {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (xbar : GeometricPoint X)
    (hφ : Function.Bijective (stalkModuleCatMap xbar φ).hom) :
    ∃ (X' : OpenSubspace X) (_ : xbar.image ∈ X'.pointsSet),
      IsIso ((pullback X'.ι).map φ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IsCoherent
