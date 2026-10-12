/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_6_14_RelativeDimension
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.6.14: in the notation and assumptions of Situation 70.6.1, let `d ≥ 0`.
If the limit base change of `f₀` has relative dimension ≤ `d` and `f₀` is locally
of finite type, then some stagewise base change `fᵢ` has relative dimension ≤ `d`
for a stage `i ≥ i₀`. -/
@[stacks 0D4K] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_relativeDimensionLE_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ),
      AlgebraicSpace.RelativeDimensionLE s.limitHom d →
        AlgebraicSpace.LocallyOfFiniteType s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            AlgebraicSpace.RelativeDimensionLE (s.stageHom i hi0i) d)
