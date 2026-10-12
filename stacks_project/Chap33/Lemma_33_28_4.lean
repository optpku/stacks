/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.IntegralClosure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.28.4: for a connected reduced scheme over a field, the integral closure of the
base field in its global sections is a field. -/
@[stacks 04MI]
#check (AlgebraicGeometry.Scheme.Hom.integralClosure_isField_of_connectedReduced :
  ∀ {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] [IsReduced X],
    IsField (integralClosure k (AlgebraicGeometry.Scheme.Hom.globalSectionsAlg f)))
