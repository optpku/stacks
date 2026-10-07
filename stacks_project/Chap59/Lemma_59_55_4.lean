module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import stacks_project.Chap59.Lemma_59_55_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SheafSystem

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))

/-- Lemma 59.55.4: if `f` is integral and the square is cartesian, then for any
sheaf of sets `F` on `X` étale the comparison
`g^{-1} f_* F ⟶ f'_* (g')^{-1} F` is an isomorphism. -/
@[stacks 0EYP]
theorem integral_baseChange_isIso [IsIntegralHom f] :
    IsIso (finiteBaseChangeHom f g f' g' h_cart F) := sorry

end AlgebraicGeometry.Scheme.Etale

end

end
