/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Pullback

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.11.6: Let `f : X ⟶ Y` be a flat morphism of integral schemes and let `ℱ` be a
torsion-free quasicoherent `𝒪_Y`-module. Then `f^* ℱ` is a torsion-free `𝒪_X`-module. -/
@[stacks 0AXV] #check
  (AlgebraicGeometry.Scheme.Modules.IsTorsionFree.pullback :
    ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
      (f : X ⟶ Y) [Flat f] {ℱ : Y.Modules} [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ →
        AlgebraicGeometry.Scheme.Modules.IsTorsionFree
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℱ))
