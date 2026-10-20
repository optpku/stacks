/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.ProperSupport
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
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0)
variable (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable (F0 : X0.Modules) [F0.IsQuasicoherent] [F0.IsFiniteType]

/- Lemma 32.13.5: in the notation and assumptions of Situation 32.8.1, if the
scheme-theoretic support of the limit pullback of a finite-type quasicoherent module is proper
over the limit target and `f0` is locally of finite type, then the scheme-theoretic support of
the corresponding pullback is proper over some stage target at a stage `i ≥ i0`. -/
@[stacks 081G] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_isProper_schemeTheoreticSupport_stage_of_limit
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) F0 :
    IsProper
      ((Scheme.Modules.schemeTheoreticSupport
        ((Scheme.Modules.pullback
          (pullback.fst f0 (pullback.fst y0 (c.π.app i0)))).obj F0)).subschemeι ≫
        pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      LocallyOfFiniteType f0 →
        ∃ (i : I) (hi0i : i0 ≤ i), IsProper
          ((Scheme.Modules.schemeTheoreticSupport
            ((Scheme.Modules.pullback
              (pullback.fst f0 (pullback.fst y0 (D.map (homOfLE hi0i))))).obj F0)).subschemeι ≫
            pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

end

end AlgebraicGeometry
