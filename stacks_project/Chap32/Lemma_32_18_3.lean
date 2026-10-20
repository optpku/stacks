/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeDimension.MorphismBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.18.3: in the notation and assumptions of Situation 32.8.1, let `d ≥ 0`. If the
limit base change of `f₀` has relative dimension at most `d`, and `f₀` is locally of finite type,
then some stagewise base change has relative dimension at most `d`. -/
@[stacks 0H3V] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_relativeDimensionLE_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}} {i0 : I}
      {X0 Y0 : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
      [CompactSpace X0] [QuasiSeparatedSpace X0]
      [CompactSpace Y0] [QuasiSeparatedSpace Y0]
      [∀ {i i' : I} (h : i ≤ i'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE h))]
      (s : AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE s.limitHom d →
        AlgebraicGeometry.LocallyOfFiniteType s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE (s.stageHom i hi0i) d)
