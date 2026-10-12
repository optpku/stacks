/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Composition

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 29.37.8: for composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S` with
quasi-compact `S`, an `f`-relatively ample module tensored with the pullback of sufficiently high
tensor powers of a `g`-relatively ample module is relatively ample over `f ≫ g`. -/
@[stacks 0C4K] #check
  (AlgebraicGeometry.RelativelyAmple.eventually_comp_tensor_pullback_tensorPow :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules},
      [CompactSpace S] → RelativelyAmple g M → RelativelyAmple f L →
        ∀ᶠ a : ℕ in Filter.atTop,
          RelativelyAmple (f ≫ g)
            (L ⊗ (Scheme.Modules.pullback f).obj (RingedSpace.TensorPower.sheaf M a)))

end AlgebraicGeometry
