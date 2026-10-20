module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Integral

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.55.4: if `f` is integral and the square is cartesian, then for any
set-valued small étale sheaf `F` on `X`, the comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 0EYP] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_integral :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsIntegralHom f],
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap g f' g' f h_cart.flip F))

end
