module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Power
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.37.2: an invertible module on a scheme is relatively ample over a morphism if and
only if any positive tensor power is relatively ample over the same morphism. -/
@[stacks 02NN] #check
  (AlgebraicGeometry.relativelyAmple_iff_tensorPow_relativelyAmple :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      (L : X.Modules) [hL : Scheme.Modules.Invertible L]
      (n : ℕ) (hn : 0 < n),
      RelativelyAmple f L ↔
        RelativelyAmple f (RingedSpace.TensorPower.sheaf L n))
