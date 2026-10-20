/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Smooth
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.6.3: in the notation and assumptions of Situation 70.6.1, if the limit base
change of `f₀` is smooth and `f₀` is locally of finite presentation, then some stagewise
base change `fᵢ` is smooth for a stage `i ≥ i₀`. -/
@[stacks 0CN2] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_smooth_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      AlgebraicSpace.Smooth s.limitHom →
        AlgebraicSpace.LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Smooth (s.stageHom i hi0i))
