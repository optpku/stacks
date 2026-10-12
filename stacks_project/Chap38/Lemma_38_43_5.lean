/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.IdealSheaf.Eta.Derived

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTriple

/- Lemma 38.43.5: for a good triple, derived pullback commutes up to isomorphism
with derived ideal-sheaf eta whenever the inverse-image divisor is effective Cartier. -/
@[stacks 0F9X] #check
  (AlgebraicGeometry.Scheme.IsGoodTriple.etaPullback_isIsomorphic :
    ∀ {X Y : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
      [IsEffectiveCartierDivisor (D.comap h).subschemeι] (hgood : IsGoodTriple D M),
      IsIsomorphic
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj
          ((functor D.toSubobject).obj M))
        ((functor (D.comap h).toSubobject).obj
          ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)))

end AlgebraicGeometry.Scheme.IsGoodTriple
