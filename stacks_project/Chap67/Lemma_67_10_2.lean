/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 67.10.2 -/
@[stacks 042M] #check (AlgebraicGeometry.AlgebraicSpace.mono_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [∀ (T : (Over S)ᵒᵖ), Function.Injective (f.app T), Mono f,
      IsIso (pullback.diagonal f)])
