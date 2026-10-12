/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 31.13.12: let `f : S' ⟶ S` be a morphism of schemes and let `D` be an effective
Cartier divisor on `S`. The pullback of `D` by `f` is defined when the inverse-image closed
subscheme on `S'`, represented by `D.comap f`, is an effective Cartier divisor. -/
@[stacks 01WV] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      S.IdealSheafData → (S' ⟶ S) → Prop)

#check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_iff :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (D : S.IdealSheafData) → (f : S' ⟶ S) →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f ↔
          AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι)
