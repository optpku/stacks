/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 29.37.7 (1): tensoring an `f`-ample module with the pullback of a sufficiently high
tensor power of an ample invertible module on the base is ample. -/
@[stacks 0892] #check
  (AlgebraicGeometry.RelativelyAmple.eventually_isAmpleObject_tensor_pullback_tensorPow :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {L : X.Modules} {M : Y.Modules},
      RelativelyAmple f L → Scheme.Modules.isAmpleObject M →
        ∀ᶠ a : ℕ in Filter.atTop,
          Scheme.Modules.isAmpleObject
            (L ⊗ (Scheme.Modules.pullback f).obj (RingedSpace.TensorPower.sheaf M a)))

/- Lemma 29.37.7 (2): pullback along a quasi-affine morphism preserves ample invertible
modules. -/
@[stacks 0892] #check
  (AlgebraicGeometry.Scheme.Modules.isAmpleObject_pullback_of_quasiAffineHom :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {M : Y.Modules},
      Scheme.Modules.isAmpleObject M → QuasiAffineHom f →
        Scheme.Modules.isAmpleObject ((Scheme.Modules.pullback f).obj M))

end AlgebraicGeometry
