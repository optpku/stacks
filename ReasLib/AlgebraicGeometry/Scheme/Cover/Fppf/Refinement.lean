module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Refinements of fppf covers

Fppf covers of affine schemes have finite refinements by affine open subschemes
of their members.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Fppf

/-- An fppf cover of an affine scheme has a finite affine fppf refinement whose
component maps into the original cover are open immersions. -/
theorem exists_finite_affineRefinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.Cover Scheme.fppfPrecoverage) :
    ∃ (𝒱 : T.AffineCover
        ((@Flat) ⊓ (@LocallyOfFinitePresentation : CategoryTheory.MorphismProperty Scheme)))
        (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := sorry

end AlgebraicGeometry.Scheme.Fppf
