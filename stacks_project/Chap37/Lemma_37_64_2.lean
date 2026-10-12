/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.2: a scheme morphism is weakly étale if and only if every induced
stalk map on local rings is weakly étale. -/
@[stacks 094Q] #check
  (AlgebraicGeometry.WeaklyEtale.iff_stalkMap :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      WeaklyEtale f ↔ ∀ x : X, RingHom.WeaklyEtale (f.stalkMap x).hom)
