/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.LocallyProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.17.4: if `f : X ⟶ S` is finite type and affine, and `F` is a finite-type
quasicoherent module on `X` whose pushforward is locally projective on `S`, then `F` is
universally pure over `S`. -/
@[stacks 05K6]
#check (AlgebraicGeometry.Scheme.Modules.isUniversallyPureOver_of_pushforward_isLocallyProjective :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType] [IsAffineHom f]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
      [((Scheme.Modules.pushforward f).obj F).IsLocallyProjective],
    F.IsUniversallyPureOver f)

end AlgebraicGeometry.Scheme.Modules
