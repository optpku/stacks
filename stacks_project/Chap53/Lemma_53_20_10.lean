/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.AtWorstNodal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

open QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/- Lemma 53.20.10 -/
@[stacks 0C5F] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_atWorstNodal_stage_of_limitHom :
    ∀ (s : QcqsMorphismBaseChange D i0 X0 Y0),
      AtWorstNodal s.limitHom →
        LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), AtWorstNodal (s.stageHom i hi0i))

end AlgebraicGeometry.Scheme.Limit
