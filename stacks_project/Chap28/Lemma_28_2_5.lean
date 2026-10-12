/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.2.5: let `X` be a quasi-compact and quasi-separated scheme. Any locally constructible
subset of `X` is constructible. -/
@[stacks 054E] #check
  (Topology.IsLocallyConstructible.isConstructible :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {E : Set X}, Topology.IsLocallyConstructible E → Topology.IsConstructible E)
