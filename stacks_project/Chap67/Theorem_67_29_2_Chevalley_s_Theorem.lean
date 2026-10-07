module

public import stacks_project.Chap66.Lemma_66_8_1_Constructible
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 67.29.2 (Chevalley's Theorem): let `S` be a scheme, and let `f : X ⟶ Y` be a
quasi-compact morphism of algebraic spaces over `S` which is locally of finite presentation.
Then the image of every étale locally constructible subset of `|X|` is an étale locally
constructible subset of `|Y|`. -/
@[stacks 0ECX]
theorem IsEtaleLocallyConstructible.image {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] {E : Set (Points X)}
    (hE : IsEtaleLocallyConstructible E) :
    IsEtaleLocallyConstructible (Points.map f '' E) := sorry

end AlgebraicGeometry.AlgebraicSpace
