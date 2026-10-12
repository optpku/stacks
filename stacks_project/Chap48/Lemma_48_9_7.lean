/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.9.7: a chosen right adjoint to derived pushforward along a
pseudo-coherent closed immersion restricts to a functor naturally isomorphic to
derived internal Hom from `𝒪_Z` on bounded-below quasicoherent derived categories. -/
@[stacks 0A9X]
#check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointPlus_isomorphic_internalHom :
    ∀ {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X)
      [IsClosedImmersion i] [PseudoCoherent i]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh X ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh Z)
      (adj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn i ⊣ a),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointPlus i a adj)
        (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomPlus i))
