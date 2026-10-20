/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 : I)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]

/- Lemma 32.8.6: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f0` is separated, then some stagewise base change is separated at a stage `i ≥ i0`. -/
@[stacks 01ZQ] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_isSeparated_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    IsSeparated (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      ∃ (i : I) (hi0i : i0 ≤ i),
        IsSeparated (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

end

end AlgebraicGeometry
