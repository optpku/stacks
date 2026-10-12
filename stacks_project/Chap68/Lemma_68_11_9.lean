/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_11_9_StrictHenselization
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace

universe u

@[expose] public section

/- Lemma 68.11.9: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `xbar` be a geometric point of `X` lying over `x ∈ |X|`. The étale local ring
`etaleLocalRing X xbar` of `X` at `xbar` is a strict henselization of the henselian
local ring `henselianLocalRing X xbar.image` of `X` at the image point. -/
@[stacks 0EMZ] #check
  (etaleLocalRing.instIsStrictHenselizationOf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (xbar : GeometricPoint X),
      IsStrictHenselizationOf (henselianLocalRing X xbar.image)
        (etaleLocalRing X xbar))
