/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change along a universal homeomorphism induces an equivalence of
categories of finite étale schemes. -/
instance finiteEtaleBaseChangeIsEquivalenceOfUniversalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f) := sorry

end AlgebraicGeometry.Scheme
