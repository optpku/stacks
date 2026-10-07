module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Extending an integral morphism along a quasi-compact open immersion

An integral morphism of algebraic spaces along a quasi-compact open immersion
extends to an integral morphism of the ambient space, recovering the original
source as the inverse image of that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.9.1: Let `S` be a scheme. Let `j : V ⟶ Y` be a quasi-compact open
immersion of algebraic spaces over `S`. Let `π : Z ⟶ V` be an integral morphism.
Then there exists an integral morphism `ν : Y' ⟶ Y` such that `Z` is
`V`-isomorphic to the inverse image of `V` in `Y'`. -/
@[stacks 0G2D]
theorem exists_isIntegralHom_isPullback {S : Scheme.{u}}
    {V Y Z : AlgebraicSpace S} (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (π : Z ⟶ V) [IsIntegralHom π] :
    ∃ (Y' : AlgebraicSpace S) (ν : Y' ⟶ Y) (hν : IsIntegralHom ν) (μ : Z ⟶ Y'),
      IsPullback μ π ν j :=
  sorry

/-- A pullback square against a quasi-compact open immersion `j : V ⟶ Y` exhibits
its vertex as isomorphic over `V` to the inverse image of `V`. -/
theorem isoOver_openInverseImage_of_isPullback {S : Scheme.{u}}
    {V Y Z Y' : AlgebraicSpace S} (j : V ⟶ Y) [IsOpenImmersion j] (π : Z ⟶ V)
    (ν : Y' ⟶ Y) (μ : Z ⟶ Y') (h : IsPullback μ π ν j) :
    ∃ e : Z ≅ openInverseImage ν j, e.hom ≫ openInverseImageTo ν j = π :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
