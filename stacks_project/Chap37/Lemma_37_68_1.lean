module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Affine

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/- Lemma 37.68.1: if `Z` and `X` are affine schemes over an affine scheme `S`
and `Γ(S, ⊤) ⟶ Γ(Z, ⊤)` is finite free, then the relative-Hom presheaf
`Mor_S(Z, X)` is represented by an affine scheme over `S`. -/
@[stacks 05Y6] #check
  (AlgebraicGeometry.Scheme.RelativeHom.representableByAffineOfFiniteFree :
    ∀ {S : Scheme.{u}} [IsAffine S] (Z X : S.AffineOver),
      (Hom.appTop Z.toComma.hom).hom.FiniteFree →
        ∃ H : S.AffineOver, Nonempty ((functor Z.obj X.obj).RepresentableBy H.obj))

end AlgebraicGeometry.Scheme.RelativeHom
