/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Situation_70_6_1_MorphismBaseChange
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Descent of relative flatness along inverse limits of algebraic spaces

Relative flatness of a finitely presented quasi-coherent module, and flatness of a
locally finitely presented morphism, descend from the limit of a directed inverse
system of algebraic spaces to some stage.
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

/-- The canonical morphism `Xᵢ ⟶ X₀` from the stagewise source pullback. -/
def stageSourceMap (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    s.stageSource i hi0i ⟶ X0 :=
  pullback.fst s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The canonical morphism `X ⟶ X₀` from the limit source pullback. -/
def limitSourceMap (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitSource ⟶ X0 :=
  pullback.fst s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0))

/-- The stagewise source map is the canonical first pullback projection. -/
theorem stageSourceMap_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I)
    (hi0i : i0 ≤ i) :
    s.stageSourceMap i hi0i =
      pullback.fst s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i))) := sorry

/-- The limit source map is the canonical first pullback projection. -/
theorem limitSourceMap_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitSourceMap =
      pullback.fst s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0)) := sorry

/-- If a finitely presented quasi-coherent module becomes flat over the target after
base change to the limit of a directed inverse system, and the structure morphism is
locally of finite presentation, then the module is already flat over the stagewise
target after base change to some stage above the distinguished stage. -/
theorem exists_flatOver_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (F0 : X0.Modules)
    [F0.IsQuasicoherent] [F0.IsFinitePresentation]
    (h_limit : Modules.flatOver ((Modules.pullback s.limitSourceMap).obj F0) s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Modules.flatOver ((Modules.pullback (s.stageSourceMap i hi0i)).obj F0)
        (s.stageHom i hi0i) := sorry

/-- If a locally finitely presented morphism of algebraic spaces becomes flat after
base change to the limit of a directed inverse system, then it becomes flat after
base change to some stage above the distinguished stage. -/
theorem exists_flat_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.Flat s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Flat (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
