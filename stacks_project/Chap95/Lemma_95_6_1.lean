/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Stack
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 95.6.1: the functor `p : FÉt ⥤ (Sch/S)_fppf` defines a stack over
`(Sch/S)_fppf`. -/
@[stacks 0BLZ] #check (AlgebraicGeometry.Scheme.FiniteEtale.instIsStackOnSite :
  ∀ (S : Scheme.{u}), IsStack.OnSite (Scheme.fppfTopology.over S)
    (AlgebraicGeometry.Scheme.FiniteEtale.p S))
