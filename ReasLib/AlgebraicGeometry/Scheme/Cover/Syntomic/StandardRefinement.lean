module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSyntomic.Basic

/-!
# Standard refinements of syntomic covers

This module provides finite standard syntomic refinements of syntomic covers
of affine schemes.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.SyntomicCover

/-- Every syntomic covering of an affine scheme admits a finite refinement by
standard syntomic affine charts that are open in members of the original
covering. -/
theorem exists_standardRefinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : SyntomicCover.{u, v} T) :
    ∃ 𝒱 : StandardSyntomicCovering T,
      ∃ φ : CategoryTheory.Precoverage.ZeroHypercover.Hom
          (Scheme.precoverage (@Syntomic)) 𝒱.toSyntomicCover 𝒰,
        ∀ j : Fin 𝒱.n, IsOpenImmersion (φ.h₀ j) := sorry

end AlgebraicGeometry.SyntomicCover
