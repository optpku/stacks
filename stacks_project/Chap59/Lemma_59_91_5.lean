module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import stacks_project.Chap59.Lemma_59_55_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Etale.SheafSystem

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))

/-- Lemma 59.91.5: if `f : X ⟶ Y` is proper and `g : Y' ⟶ Y` is any morphism of
schemes, with `X'` cartesian over `Y` via projections `f'` and `g'`, then for any
sheaf of sets `F` on `X` étale the comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 0A3U]
theorem proper_baseChange_isIso [IsProper f] :
    IsIso (finiteBaseChangeHom f g f' g' h_cart F) := sorry

end AlgebraicGeometry.Scheme.Etale

end

end
