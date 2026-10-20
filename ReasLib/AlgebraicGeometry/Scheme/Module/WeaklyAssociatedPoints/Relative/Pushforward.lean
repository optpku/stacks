/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative
import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z S : Scheme.{u}}

/-- Finite pushforward carries the relative weak assassin of a quasicoherent module exactly to
its image under the underlying map of schemes. -/
@[stacks 0CUD]
theorem relativeWeakAss_pushforward_eq_image_of_isFinite
    (f : X ⟶ S) (i : Z ⟶ X) [IsFinite i]
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    relativeWeakAss f ((Scheme.Modules.pushforward i).obj ℱ) =
      i.base '' relativeWeakAss (i ≫ f) ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
