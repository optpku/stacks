module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.7.1: for an affine morphism of schemes, derived quasicoherent pushforward
commutes, up to natural isomorphism, with the canonical comparisons to derived modules
having quasicoherent cohomology. -/
@[stacks 08D7] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardComparison_isomorphic_of_isAffineHom :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.QCoh.Derived.pushforward f ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.comparison Y)
        (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f))

#check AlgebraicGeometry.Scheme.QCoh.Derived.pushforward
#check AlgebraicGeometry.Scheme.QCoh.Derived.pushforwardIsRightDerived

end AlgebraicGeometry.Scheme.DerivedQCoh
