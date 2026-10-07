module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Tensor

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.5: if `L` and `M` are invertible `𝒪_X`-modules, `L` is ample, and the
nonvanishing opens of positive tensor powers of `M` cover `X`, then `L ⊗ M` is ample. -/
@[stacks 0890] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_tensor_of_isAmple_of_nonvanishing_cover :
    ∀ {X : Scheme.{u}} (L M : X.Modules)
      [hL : AlgebraicGeometry.Scheme.Modules.Invertible L]
      [hM : AlgebraicGeometry.Scheme.Modules.Invertible M]
      [AlgebraicGeometry.Scheme.Modules.IsAmple L],
      (∀ x : X, ∃ m : ℕ, 0 < m ∧
        ∃ t : Γ(RingedSpace.TensorPower.sheaf M m, ⊤),
          x ∈ (hM.nonvanishingOpen t : Set X)) →
      AlgebraicGeometry.Scheme.Modules.IsAmple (L ⊗ M))
