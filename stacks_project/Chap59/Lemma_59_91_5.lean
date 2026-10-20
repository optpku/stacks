module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.91.5: if `f : X ⟶ Y` is proper and `g : Y' ⟶ Y` is any morphism of
schemes, with `X'` cartesian over `Y` via projections `f'` and `g'`, then for any
sheaf of sets `F` on `X` étale the comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 0A3U] #check (AlgebraicGeometry.Scheme.Etale.proper_baseChange_isIso :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsProper f],
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap g f' g' f h_cart.flip F))

end
