/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Situation_70_6_1_MorphismBaseChange
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- If a morphism of algebraic spaces that is locally of finite type becomes
proper after base change to the limit of a directed inverse system, then it
becomes proper after base change to some stage above the distinguished stage. -/
theorem exists_proper_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.Proper s.limitHom)
    (h_finiteType : AlgebraicSpace.LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Proper (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
