/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.10.3: A monomorphism of algebraic spaces is separated. -/
@[stacks 042N] #check (AlgebraicGeometry.AlgebraicSpace.Separated.of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f],
    AlgebraicGeometry.AlgebraicSpace.Separated f)
