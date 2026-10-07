module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap97.Lemma_97_9_2_Section

/-!
# Spaces of sections of étale morphisms onto finite locally free schemes

If `π : Z ⟶ U` is finite locally free and `W ⟶ Z` is étale, the functor of
sections of `W_T ⟶ Z_T` is an algebraic space étale over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.SpaceOfSections

variable {U Z : Scheme.{u}} {W : AlgebraicSpace U}

/-- Lemma 97.9.2 (1): Let `π : Z ⟶ U` be a finite locally free morphism of schemes,
and let `W` be an algebraic space over `U` with an étale morphism
`f : W ⟶ ofOver (Over.mk π)`. Then the functor of sections of `W_T ⟶ Z_T` is an
algebraic space. -/
@[stacks 05XR, instance]
instance instIsAlgebraicSpace (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    IsAlgebraicSpace (functor π f) :=
  sorry

/-- The algebraic space associated to the functor of sections of `f`. -/
def space (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] : AlgebraicSpace U :=
  ofIsAlgebraicSpace (functor π f)

/-- The functor of points of `space π f` is `functor π f`. -/
theorem space_functorOfPoints (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    (space π f).functorOfPoints = functor π f :=
  sorry

/-- Lemma 97.9.2 (2): Let `π : Z ⟶ U` be a finite locally free morphism of schemes,
and let `W` be an algebraic space over `U` with an étale morphism
`f : W ⟶ ofOver (Over.mk π)`. Then the structure morphism
`toBase (space π f)` is étale. -/
@[stacks 05XR, instance]
instance instEtale_toBase (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    Etale (toBase (space π f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SpaceOfSections
