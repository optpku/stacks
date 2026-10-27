/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback

/-!
# External tensor products of modules on algebraic spaces

The canonical external tensor product `p₁^* F ⊗ p₂^* G` on a fibre product
of algebraic spaces over a common base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The external tensor product `p₁^* F ⊗ p₂^* G` on the fibre product of two
algebraic spaces over a common base. -/
abbrev externalTensorProduct {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (F : X.Modules) (G : Y.Modules) :
    (Limits.pullback f g).Modules :=
  tensorObj ((pullback (Limits.pullback.fst f g)).obj F)
    ((pullback (Limits.pullback.snd f g)).obj G)

/-- `externalTensorProduct f g F G` is the tensor of the pullbacks of `F` and
`G` along the projections of the fibre product. -/
theorem externalTensorProduct_eq {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (F : X.Modules) (G : Y.Modules) :
    externalTensorProduct f g F G =
      (pullback (Limits.pullback.fst f g)).obj F ⊗
        (pullback (Limits.pullback.snd f g)).obj G := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
