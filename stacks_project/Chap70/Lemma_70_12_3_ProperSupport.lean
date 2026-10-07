module

public import stacks_project.Chap70.Situation_70_6_1_MorphismBaseChange
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Lemma_67_15_2

/-!
# Descent of properness of scheme-theoretic support

Properness of the scheme-theoretic support of a finite-type quasi-coherent
module, after pullback along a locally finite type morphism, descends from the
limit of a directed inverse system of algebraic spaces to some stage.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- If a finite-type quasi-coherent module on the source of a locally finite type
morphism of algebraic spaces has scheme-theoretic support proper over the limit
target after pullback to the limit source, then after pullback to some stage
the scheme-theoretic support is proper over the stagewise target. -/
theorem exists_proper_schemeTheoreticSupport_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (F0 : X0.Modules)
    [F0.IsQuasicoherent] [F0.IsFiniteType]
    (h_limit : AlgebraicSpace.Proper
      ((Modules.schemeTheoreticSupport
        ((Modules.pullback (pullback.fst s.hom
          (pullback.fst s.targetMap (s.limitCone.cone.π.app i0)))).obj F0)).ι ≫
        s.limitHom))
    (h_finiteType : AlgebraicSpace.LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Proper
      ((Modules.schemeTheoreticSupport
        ((Modules.pullback (pullback.fst s.hom
          (pullback.fst s.targetMap (D.map (homOfLE hi0i))))).obj F0)).ι ≫
        s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
