module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap75.Lemma_75_12_2_ArtinianPushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Lemma 75.12.2. Let `S` be an affine scheme. Let `X` be a Noetherian algebraic
space over `S`. Every injective object of `QCoh X` is a direct summand of a small
filtered colimit of quasi-coherent sheaves of the form `(Z_i ⟶ X)_* G_i`, where
each `Z_i` is the spectrum of an Artinian ring and each `G_i` is a coherent
module on `Z_i`. -/
@[stacks 09TJ]
theorem injective_retractClosure_ind_artinianSpecCoherentPushforward
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} [IsNoetherian X]
    (J : QCoh X) [Injective J] :
    (isArtinianSpecCoherentPushforward X).ind.{u}.retractClosure J :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
