module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.68.4: if `Z ⟶ S` is finite locally free and `X ⟶ S` is separated
and locally quasi-finite, then `Mor_S(Z, X)` is representable by a scheme over `S`. -/
@[stacks 0BL5] #check
  (AlgebraicGeometry.Scheme.RelativeHom.isRepresentableOfSeparatedLocallyQuasiFinite :
    ∀ {S : Scheme.{u}} (Z X : Over S),
      [IsFiniteLocallyFree Z.hom] → [IsSeparated X.hom] →
        [LocallyOfFiniteType X.hom] → [LocallyQuasiFinite X.hom] →
          (AlgebraicGeometry.Scheme.RelativeHom.functor Z X).IsRepresentable)
