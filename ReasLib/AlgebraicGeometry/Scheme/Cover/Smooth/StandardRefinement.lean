module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSmooth

/-!
# Standard smooth refinements of smooth covering families

This module provides finite standard smooth refinements of smooth covering
families of affine schemes.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.SmoothCovering

/-- Every smooth covering family of an affine scheme admits a finite refinement
by standard smooth affine charts that are open in members of the original
covering family. -/
theorem exists_standardSmoothRefinement
    {T : Scheme.{u}} [IsAffine T] {ι : Type v} {family : ι → CategoryTheory.Over T}
    (hfamily : SmoothCovering family) :
    ∃ 𝒱 : StandardSmoothCovering T,
      ∃ φ : CategoryTheory.SemiRepresentableFamily.Over.Hom 𝒱.toOverFamily
          (CategoryTheory.SemiRepresentableFamily.Over.ofArrows
            (fun i : ι ↦ (family i).left) (fun i ↦ (family i).hom)),
        ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f j).left) := sorry

end AlgebraicGeometry.Scheme.SmoothCovering
