/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_6_12_Flat
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.6.12 (1): in the notation and assumptions of Situation 70.6.1, let `F₀` be a
quasi-coherent module of finite presentation on `X₀`, write `Fᵢ` and `F` for its pullbacks
along `stageSourceMap` and `limitSourceMap`, and assume `f₀` is locally of finite
presentation. If `F` is flat over `Y`, then `Fᵢ` is flat over `Yᵢ` for some stage `i ≥ i₀`. -/
@[stacks 08K0] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_flatOver_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0)
      (F0 : X0.Modules) [F0.IsQuasicoherent] [F0.IsFinitePresentation],
      AlgebraicSpace.Modules.flatOver
        ((AlgebraicSpace.Modules.pullback s.limitSourceMap).obj F0) s.limitHom →
        AlgebraicSpace.LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            AlgebraicSpace.Modules.flatOver
              ((AlgebraicSpace.Modules.pullback (s.stageSourceMap i hi0i)).obj F0)
              (s.stageHom i hi0i))

/- Lemma 70.6.12 (2): in the notation and assumptions of Situation 70.6.1, if the limit
base change of `f₀` is flat and `f₀` is locally of finite presentation, then some
stagewise base change `fᵢ` is flat for a stage `i ≥ i₀`. -/
@[stacks 08K0] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_flat_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      AlgebraicSpace.Flat s.limitHom →
        AlgebraicSpace.LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Flat (s.stageHom i hi0i))
