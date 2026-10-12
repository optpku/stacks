/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_3_2_BoundedBelow
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 86.3.2: a chosen right adjoint to derived quasicoherent pushforward along a
morphism of quasi-compact quasi-separated algebraic spaces has a uniform lower
cohomological bound. Here `K.obj.IsGE (c + 1)` means that `Hⁱ(K) = 0` for `i ≤ c`,
and the conclusion gives vanishing for `a.obj K` in degrees `i ≤ c - N`. -/
@[stacks 0E56] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_uniformLowerBound :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
      (f : X ⟶ Y) →
      (a : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh Y ⥤
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X) →
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward f ⊣ a) →
      ∃ N : ℤ, ∀ (K : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh Y) (c : ℤ),
        K.obj.IsGE (c + 1) → (a.obj K).obj.IsGE (c - N + 1))
