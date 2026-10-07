module

public import stacks_project.Chap86.Lemma_86_3_1_RightAdjoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 86.3.1: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated
algebraic spaces over a scheme `S`, derived pushforward on `DerivedQCoh` has a
right adjoint. -/
@[stacks 0E55] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardIsLeftAdjoint :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward f).IsLeftAdjoint)
