module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.AffineDiagonal

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

/- Lemma 75.11.6. Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Assume `X` and `Y` are quasi-compact and have affine diagonal over
`ℤ` (as in Properties of Spaces, Definition 66.3.1). Then the right-derived functor
`Φ` of quasi-coherent `f_*` makes the square comparing `D(QCoh 𝒪_X)` with
`D_QCoh(𝒪_X)` and `D(QCoh 𝒪_Y)` with `D_QCoh(𝒪_Y)` commute, up to natural
isomorphism with restricted ambient `Rf_*`. -/
@[stacks 0CSR] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardComparison_isomorphic_of_compact_affineDiagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsQuasiCompact Y]
      [IsAbsolutelyAffineDiagonal X] [IsAbsolutelyAffineDiagonal Y],
      IsIsomorphic
        (QCoh.Derived.pushforward f ⋙ DerivedQCoh.comparison Y)
        (DerivedQCoh.comparison X ⋙ DerivedQCoh.pushforwardCohomologyIn f))

#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforward
#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardIsRightDerived
