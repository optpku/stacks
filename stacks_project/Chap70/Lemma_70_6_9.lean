module

public import stacks_project.Chap70.Lemma_70_6_9_Separated
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.6.9: in the notation and assumptions of Situation 70.6.1, if the limit base
change of `f₀` is separated, then some stagewise base change `fᵢ` is separated for a
stage `i ≥ i₀`. -/
@[stacks 0851] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_separated_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      AlgebraicSpace.Separated s.limitHom →
        ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Separated (s.stageHom i hi0i))
