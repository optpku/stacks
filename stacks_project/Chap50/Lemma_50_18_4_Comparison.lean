module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/- Compatibility bridge for the determinant-twisted differential-form comparison API. -/
#check (absoluteFormComparison :
  ∀ {X' X : Scheme.{u}} (g : X' ⟶ X) (p : ℕ),
    (RingedSpace.Hom.pullback g.toShHom).obj
        (Λ[p] Ω[(terminal.from X).toShHom]) ⟶
      Λ[p] Ω[(terminal.from X').toShHom])

end AlgebraicGeometry.Scheme.RelativeDifferentials
