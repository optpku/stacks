module

public import stacks_project.Chap70.Situation_70_6_1_MorphismBaseChange
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import Mathlib.CategoryTheory.MorphismProperty.Representable

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

/-- If a locally finitely presented morphism of algebraic spaces, whose
structure morphisms to a distinguished stage are representable, becomes an
isomorphism after base change to the limit of a directed inverse system of
quasi-compact, absolutely quasi-separated algebraic spaces, then it becomes an
isomorphism after base change to some stage above the distinguished stage,
provided the source and target are themselves absolutely quasi-separated. -/
theorem exists_isIso_stage_of_limitHom_of_relativelyRepresentable
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_quasiCompact : ∀ j, IsQuasiCompact (D.obj j))
    (h_absolutelyQuasiSeparated : ∀ j, IsAbsolutelyQuasiSeparated (D.obj j))
    (h_source_absolutelyQuasiSeparated : IsAbsolutelyQuasiSeparated X0)
    (h_target_absolutelyQuasiSeparated : IsAbsolutelyQuasiSeparated Y0)
    (h_source : yoneda.relativelyRepresentable s.sourceMap)
    (h_target : yoneda.relativelyRepresentable s.targetMap)
    (h_limit : IsIso s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsIso (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
