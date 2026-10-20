/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Finite
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.6.7: in the notation and assumptions of Situation 70.6.1, if the limit base
change of `f₀` is finite and `f₀` is locally of finite type, then some stagewise
base change `fᵢ` is finite for a stage `i ≥ i₀`. -/
@[stacks 084Z] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_isFinite_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      AlgebraicSpace.IsFinite s.limitHom →
        AlgebraicSpace.LocallyOfFiniteType s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.IsFinite (s.stageHom i hi0i))
