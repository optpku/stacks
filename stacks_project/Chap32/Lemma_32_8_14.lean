/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Mono
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
variable [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
variable [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
variable [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]

/- Lemma 32.8.14: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f0` is a monomorphism and `f0` is locally of finite type, then some stagewise
base change `f_i` is a monomorphism for a stage `i ≥ i0`. -/
@[stacks 07RQ] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_mono_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    Mono (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      LocallyOfFiniteType f0 →
        ∃ (i : I) (hi0i : i0 ≤ i),
          Mono (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

end

end AlgebraicGeometry
