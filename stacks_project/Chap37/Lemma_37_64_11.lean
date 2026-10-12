/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.StrictHenselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.11: a scheme morphism is weakly étale exactly when every stalk map
induces isomorphisms on compatible strict henselizations. -/
@[stacks 094Z] #check
  (AlgebraicGeometry.WeaklyEtale.iff_stalkMap_isIsoOnStrictHenselizations :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), WeaklyEtale f ↔
      ∀ x : X, (f.stalkMap x).hom.IsIsoOnStrictHenselizations)
