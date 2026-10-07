module

public import stacks_project.Chap70.Situation_70_6_1_MorphismBaseChange
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

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

/-- If a locally finitely presented morphism of algebraic spaces becomes smooth
after base change to the limit of a directed inverse system, then it becomes
smooth after base change to some stage above the distinguished stage. -/
theorem exists_smooth_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.Smooth s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Smooth (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
