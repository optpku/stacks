module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral morphism to the source of a quasi-compact open immersion of algebraic spaces
over a scheme extends to an integral morphism to its target, with the original morphism
recovered by pullback along the open immersion. -/
theorem exists_isIntegralHom_isPullback {S : Scheme.{u}}
    {V Y Z : AlgebraicSpace S} (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (π : Z ⟶ V) [IsIntegralHom π] :
    ∃ (Y' : AlgebraicSpace S) (ν : Y' ⟶ Y) (hν : IsIntegralHom ν) (μ : Z ⟶ Y'),
      IsPullback μ π ν j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
