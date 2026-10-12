/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.OpenSubspace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u

/- Lemma 74.13.2: a proper morphism of algebraic spaces and an invertible module on
the source admit an open subspace of the target through which a test morphism
factors if and only if the pulled-back module is relatively ample on the base
change. -/
@[stacks 0D3D] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.exists_openSubspace_factorsThrough_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
      (L : X.Modules) [isInvertibleObject L],
      ∃ V : OpenSubspace Y, ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        (∃ χ : Y' ⟶ V.X, χ ≫ V.ι = g) ↔
          RelativelyAmple (pullback.snd f g)
            ((Modules.pullback (pullback.fst f g)).obj L))
