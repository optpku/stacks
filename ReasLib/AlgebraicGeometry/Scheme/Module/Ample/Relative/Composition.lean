/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Tensor

/-!
# Relative Ampleness and Composition

This file records relative ampleness over a composite after tensoring with sufficiently high
pulled-back tensor powers.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If a module is relatively ample for the first of two composable morphisms and a module on
the intermediate scheme is relatively ample for the second, then sufficiently high pulled-back
tensor powers of the latter, tensored with the former, are relatively ample for the composite. -/
theorem RelativelyAmple.eventually_comp_tensor_pullback_tensorPow
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}
    [CompactSpace S] (hM : RelativelyAmple g M) (hL : RelativelyAmple f L) :
    ∀ᶠ a : ℕ in Filter.atTop,
      RelativelyAmple (f ≫ g)
        (L ⊗ (Scheme.Modules.pullback f).obj (RingedSpace.TensorPower.sheaf M a)) := sorry

end AlgebraicGeometry
