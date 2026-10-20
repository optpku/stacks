module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- Every smooth morphism admits an affine étale cover whose maps to the base factor
through affine schemes by split smooth morphisms with geometrically connected fibres,
followed by étale morphisms. -/
theorem exists_affineEtaleCover_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    ∃ 𝒰 : X.AffineCover (@Etale), ∀ i : 𝒰.I₀,
      ∃ (V : Scheme.{u}) (_ : IsAffine V)
        (p : 𝒰.cover.X i ⟶ V) (q : V ⟶ S)
        (_ : Smooth p) (_ : Etale q)
        (s : V ⟶ 𝒰.cover.X i) (_ : s ≫ p = 𝟙 V)
        (_ : GeometricallyConnected p),
        p ≫ q = 𝒰.cover.f i ≫ f := sorry

end AlgebraicGeometry.Smooth
