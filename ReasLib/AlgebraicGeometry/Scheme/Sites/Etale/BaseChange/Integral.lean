module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- Direct image along an integral morphism commutes with inverse image in a
cartesian square of schemes for set-valued small étale sheaves. -/
theorem setMap_isIso_of_integral {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsIntegralHom f] :
    IsIso (setMap g f' g' f h_cart.flip F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange
