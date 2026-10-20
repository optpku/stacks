/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Logic.Small.Set
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Brown representability from a small detecting set

The seed coproduct ranges over generator-element pairs; successor cones kill the kernel
morphisms. Their telescope defines an approximation object and a compatible element, hence an
additive Yoneda transformation. The coproduct indexing universe is independent of the object
universe, with explicit smallness conditions on the seed and kernel indices.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Pretriangulated

universe w v u v₁ v₂ u₁ u₂

namespace CategoryTheory.BrownRepresentability.SmallSet

variable {D : Type u} [Category.{v} D]

section CoproductElements

variable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})

set_option backward.privateInPublic true in
private def coproductElementsIsLimit {I : Type w} (X : I → D) [HasCoproduct X]
    [PreservesLimitsOfShape (Discrete I) H] :
    IsLimit (Fan.mk ((H ⋙ forget _).obj (op (∐ X)))
      (fun i ↦ (H ⋙ forget _).map (Sigma.ι X i).op) :
      Fan (fun i ↦ (H ⋙ forget _).obj (op (X i)))) :=
  isLimitFanMkObjOfIsLimit (H ⋙ forget _) (fun i ↦ op (X i)) _
    (Cofan.IsColimit.op (coproductIsCoproduct X))

set_option backward.privateInPublic true in
private def coproductElement {I : Type w} (X : I → D) [HasCoproduct X]
    [PreservesLimitsOfShape (Discrete I) H]
    (a : ∀ i, H.obj (op (X i))) : H.obj (op (∐ X)) :=
  (Fan.IsLimit.lift (coproductElementsIsLimit H X)
    (A := PUnit.{v + 1}) (fun i ↦ ↾fun _ ↦ a i)) PUnit.unit

set_option backward.privateInPublic true in
private theorem coproductElement_ι {I : Type w} (X : I → D) [HasCoproduct X]
    [PreservesLimitsOfShape (Discrete I) H]
    (a : ∀ i, H.obj (op (X i))) (i : I) :
    H.map (Sigma.ι X i).op (coproductElement H X a) = a i := by
  exact congrArg (fun f ↦ f PUnit.unit)
    (Fan.IsLimit.fac (coproductElementsIsLimit H X) (fun i ↦ ↾fun _ : PUnit.{v + 1} ↦ a i) i)

variable [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]

set_option backward.privateInPublic true in
private theorem preservesNatProducts : PreservesLimitsOfShape (Discrete ℕ) H :=
  preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{w}) H

end CoproductElements

section Cones

variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

set_option backward.privateInPublic true in
private def coneObject {X Y : D} (f : X ⟶ Y) : D :=
  (distinguished_cocone_triangle f).choose

set_option backward.privateInPublic true in
private def coneInclusion {X Y : D} (f : X ⟶ Y) : Y ⟶ coneObject f :=
  (distinguished_cocone_triangle f).choose_spec.choose

set_option backward.privateInPublic true in
private def coneConnecting {X Y : D} (f : X ⟶ Y) : coneObject f ⟶ X⟦(1 : ℤ)⟧ :=
  (distinguished_cocone_triangle f).choose_spec.choose_spec.choose

set_option backward.privateInPublic true in
private theorem cone_distinguished {X Y : D} (f : X ⟶ Y) :
    Triangle.mk f (coneInclusion f) (coneConnecting f) ∈ distTriang D :=
  (distinguished_cocone_triangle f).choose_spec.choose_spec.choose_spec

variable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.rightOp.IsHomological]
set_option backward.privateInPublic true in
private theorem exists_lift {X Y : D} (f : X ⟶ Y) (a : H.obj (op Y))
    (ha : H.map f.op a = 0) :
    ∃ b : H.obj (op (coneObject f)), H.map (coneInclusion f).op b = a := by
  have hS := (H.rightOp.map_distinguished_exact _ (cone_distinguished f)).unop
  exact (ShortComplex.ab_exact_iff _).mp hS a ha

set_option backward.privateInPublic true in
private theorem map_sub_apply {X Y : D} (f g : X ⟶ Y) (a : H.obj (op Y)) :
    H.map (f - g).op a = H.map f.op a - H.map g.op a := by
  change ((H.rightOp.map (f - g)).unop) a = _
  rw [H.rightOp.map_sub]
  rfl

end Cones

section Kernel

variable [HasCoproducts.{w} D] [LocallySmall.{w} D]
variable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (S : Set D) [Small.{w} S]

set_option backward.privateInPublic true in
private abbrev kernelPairs (X : D) (a : H.obj (op X)) :=
  Σ E : S, {f : E.1 ⟶ X // H.map f.op a = 0}

set_option backward.privateInPublic true in
private def kernelFamily (X : D) (a : H.obj (op X)) :
    Shrink.{w} (kernelPairs H S X a) → D :=
  fun i ↦ ((equivShrink (kernelPairs H S X a)).symm i).1.1

set_option backward.privateInPublic true in
/-- The coproduct of generators indexed by morphisms annihilating a specified element. -/
def kernelObject (X : D) (a : H.obj (op X)) : D :=
  ∐ (kernelFamily H S X a)

set_option backward.privateInPublic true in
/-- The map from the kernel-indexed coproduct to the current approximation object. -/
def kernelMap (X : D) (a : H.obj (op X)) : kernelObject H S X a ⟶ X :=
  Sigma.desc (fun i ↦ ((equivShrink (kernelPairs H S X a)).symm i).2.1)

variable [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- The kernel-indexed coproduct map annihilates its defining element. -/
theorem kernelMap_element (X : D) (a : H.obj (op X)) :
    H.map (kernelMap H S X a).op a = 0 := by
  apply Concrete.isLimit_ext _ (coproductElementsIsLimit H (kernelFamily H S X a))
  intro i
  change H.map (Sigma.ι (kernelFamily H S X a) i.as).op
    (H.map (kernelMap H S X a).op a) = H.map _ 0
  dsimp only [kernelObject, kernelMap]
  simp only [map_zero, ← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp]
  simp only [Sigma.ι_desc]
  exact ((equivShrink (kernelPairs H S X a)).symm i.as).2.2

end Kernel

section Approximation

variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{w} D] [LocallySmall.{w} D]
variable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.rightOp.IsHomological]
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
variable (S : Set D) [Small.{w} S] [∀ E : S, Small.{w} (H.obj (op E.1))]

set_option backward.privateInPublic true in
private def successor (p : Σ X : D, H.obj (op X)) : Σ X : D, H.obj (op X) :=
  ⟨coneObject (kernelMap H S p.1 p.2),
    (exists_lift H (kernelMap H S p.1 p.2) p.2 (kernelMap_element H S p.1 p.2)).choose⟩

set_option backward.privateInPublic true in
private abbrev seedPairs := Σ E : S, H.obj (op E.1)

set_option backward.privateInPublic true in
private def seedFamily : Shrink.{w} (seedPairs H S) → D :=
  fun i ↦ ((equivShrink (seedPairs H S)).symm i).1.1

set_option backward.privateInPublic true in
private def seedValue (i : Shrink.{w} (seedPairs H S)) : H.obj (op (seedFamily H S i)) :=
  ((equivShrink (seedPairs H S)).symm i).2

set_option backward.privateInPublic true in
private def stagePair : ℕ → Σ X : D, H.obj (op X)
  | 0 => ⟨∐ (seedFamily H S), coproductElement H (seedFamily H S) (seedValue H S)⟩
  | n + 1 => successor H S (stagePair n)

set_option backward.privateInPublic true in
/-- The object at stage `n` of the Brown approximation tower, with the seed at stage zero. -/
def stage (n : ℕ) : D := (stagePair H S n).1

set_option backward.privateInPublic true in
/-- The compatible element of the functor at the `n`th approximation stage. -/
def stageElement (n : ℕ) : H.obj (op (stage.{w} H S n)) := (stagePair H S n).2

set_option backward.privateInPublic true in
/-- The successor map obtained by taking the cone of the kernel-indexed coproduct map. -/
def transition (n : ℕ) : stage.{w} H S n ⟶ stage.{w} H S (n + 1) :=
  coneInclusion (kernelMap H S (stage.{w} H S n) (stageElement.{w} H S n))

set_option backward.privateInPublic true in
/-- Pullback along a successor map recovers the preceding stage element. -/
lemma transition_element (n : ℕ) :
    H.map (transition.{w} H S n).op (stageElement.{w} H S (n + 1)) = stageElement.{w} H S n :=
  (exists_lift H (kernelMap H S (stage.{w} H S n) (stageElement.{w} H S n))
    (stageElement.{w} H S n) (kernelMap_element H S _ _)).choose_spec

set_option backward.privateInPublic true in
/-- The sequential diagram of Brown approximation stages and their successor maps. -/
abbrev tower : ℕ ⥤ D := Functor.ofSequence (transition.{w} H S)

set_option backward.privateInPublic true in
private abbrev towerCoproduct : ColimitCocone (Discrete.functor (tower.{w} H S).obj) :=
  getColimitCocone _

set_option backward.privateInPublic true in
private def telescope : ∐ (tower.{w} H S).obj ⟶ ∐ (tower.{w} H S).obj :=
  Sequential.CoproductCocone.telescopeMap (tower.{w} H S) (towerCoproduct.{w} H S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private theorem ι_telescope (n : ℕ) :
    Sigma.ι (tower.{w} H S).obj n ≫ telescope.{w} H S =
      Sigma.ι (tower.{w} H S).obj n - (tower.{w} H S).map (homOfLE (Nat.le_succ n)) ≫
        Sigma.ι (tower.{w} H S).obj (n + 1) := by
  change Sigma.ι (tower.{w} H S).obj n ≫ Sigma.desc _ = _
  exact (Sigma.ι_desc (fun n ↦ Sigma.ι (tower.{w} H S).obj n -
      (tower.{w} H S).map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι (tower.{w} H S).obj (n + 1)) n)

set_option backward.privateInPublic true in
private def towerElement : H.obj (op (∐ (tower.{w} H S).obj)) := by
  -- Local instance justification (proof-local temporary data): restrict the supplied product
  -- preservation to the countable telescope index.
  letI : PreservesLimitsOfShape (Discrete ℕ) H := preservesNatProducts H
  exact coproductElement H (tower.{w} H S).obj (stageElement.{w} H S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private theorem towerElement_ι (n : ℕ) :
    H.map (Sigma.ι (tower.{w} H S).obj n).op (towerElement.{w} H S) = stageElement.{w} H S n := by
  -- Local instance justification (proof-local temporary data): the same countable
  -- product-preservation instance used to assemble the tower element.
  letI : PreservesLimitsOfShape (Discrete ℕ) H := preservesNatProducts H
  exact coproductElement_ι H (tower.{w} H S).obj (stageElement.{w} H S) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private theorem telescope_zero : H.map (telescope.{w} H S).op (towerElement.{w} H S) = 0 := by
  -- Local instance justification (proof-local temporary data): use preserved countable
  -- products to test equality at every stage.
  letI : PreservesLimitsOfShape (Discrete ℕ) H := preservesNatProducts H
  apply Concrete.isLimit_ext _ (coproductElementsIsLimit H (tower.{w} H S).obj)
  intro n
  change H.map (Sigma.ι (tower.{w} H S).obj n.as).op
    (H.map (telescope.{w} H S).op (towerElement.{w} H S)) = H.map _ 0
  rw [map_zero]
  refine (congrArg (fun k ↦ k (towerElement.{w} H S))
    (H.map_comp (telescope.{w} H S).op (Sigma.ι (tower.{w} H S).obj n.as).op)).symm.trans ?_
  change H.map ((Sigma.ι (tower.{w} H S).obj n.as ≫ telescope.{w} H S).op)
    (towerElement.{w} H S) = 0
  rw [ι_telescope, map_sub_apply, towerElement_ι.{w} H S n.as]
  rw [op_comp, H.map_comp, ConcreteCategory.comp_apply, towerElement_ι.{w} H S (n.as + 1),
    Functor.ofSequence_map_homOfLE_succ]
  exact sub_eq_zero.mpr (transition_element.{w} H S n.as).symm

set_option backward.privateInPublic true in
/-- The homotopy colimit of the Brown approximation tower. -/
def approximationObject : D := coneObject (telescope.{w} H S)

set_option backward.privateInPublic true in
/-- The distinguished telescope triangle of the Brown approximation object. -/
def approximationPresentation :
    HomotopyColimit.Presentation (tower.{w} H S) (approximationObject.{w} H S) where
  coproduct := towerCoproduct.{w} H S
  toCocone := coneInclusion (telescope.{w} H S)
  connecting := coneConnecting (telescope.{w} H S)
  distinguished := cone_distinguished (telescope.{w} H S)

set_option backward.privateInPublic true in
/-- A lift of the compatible stage elements through the distinguished telescope triangle. -/
def approximationElement : H.obj (op (approximationObject.{w} H S)) :=
  (exists_lift H (telescope.{w} H S) (towerElement.{w} H S) (telescope_zero H S)).choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- The lifted telescope element restricts to the selected element at each stage. -/
lemma approximationElement_ι (n : ℕ) :
    H.map ((approximationPresentation.{w} H S).ι n).op (approximationElement.{w} H S) =
      stageElement.{w} H S n := by
  change H.map (Sigma.ι (tower.{w} H S).obj n ≫ coneInclusion (telescope.{w} H S)).op _ = _
  rw [op_comp, H.map_comp, ConcreteCategory.comp_apply]
  have hlift : H.map (coneInclusion (telescope.{w} H S)).op (approximationElement.{w} H S) =
      towerElement.{w} H S :=
    (exists_lift H (telescope.{w} H S) (towerElement.{w} H S) (telescope_zero H S)).choose_spec
  exact (congrArg (fun a ↦ H.map (Sigma.ι (tower.{w} H S).obj n).op a) hlift).trans
    (towerElement_ι H S n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- The additive Yoneda transformation induced by the lifted approximation element. -/
def comparison : preadditiveYoneda.obj (approximationObject.{w} H S) ⟶ H where
  app Y := AddCommGrpCat.ofHom
    { toFun := fun f ↦ H.map f.op (approximationElement.{w} H S)
      map_zero' := by
        change ((H.rightOp.map 0).unop) (approximationElement.{w} H S) = 0
        rw [H.rightOp.map_zero]
        rfl
      map_add' := by
        intro f g
        change ((H.rightOp.map (f + g)).unop) (approximationElement.{w} H S) = _
        rw [H.rightOp.map_add]
        rfl }
  naturality := by
    intro X Y f
    ext g
    change H.map (f.unop ≫ g).op (approximationElement.{w} H S) =
      H.map f (H.map g.op (approximationElement.{w} H S))
    rw [op_comp, H.map_comp]
    rfl

end Approximation

section ApproximationLaws

variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{w} D] [LocallySmall.{w} D]
variable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.rightOp.IsHomological]
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
variable (S : Set D) [Small.{w} S] [∀ E : S, Small.{w} (H.obj (op E.1))]

set_option backward.privateInPublic true in
/-- Each successor map kills the kernel-indexed coproduct map from which it was constructed. -/
theorem kernelMap_comp_transition (n : ℕ) :
    kernelMap H S (stage.{w} H S n) (stageElement.{w} H S n) ≫ transition.{w} H S n = 0 :=
  comp_distTriang_mor_zero₁₂ _ (cone_distinguished _)

/-- Evaluation of the approximation comparison is pullback of the lifted element. -/
@[simp]
theorem comparison_app (Y : D) (f : Y ⟶ approximationObject.{w} H S) :
    (comparison.{w} H S).app (op Y) f = H.map f.op (approximationElement.{w} H S) := rfl

end ApproximationLaws

section Criterion

variable [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{w} D]

/-- A Brown set that is small in the coproduct universe represents every contravariant
homological functor preserving products indexed in that universe. -/
@[stacks 0GYG "small-set representability criterion"]
theorem existsRepresentation
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (hH : H.rightOp.IsHomological)
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Type-valued representability supplied by a Brown set small in the coproduct universe. -/
@[stacks 0GYG "small-set underlying representability"]
theorem isRepresentable
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (hH : H.rightOp.IsHomological)
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  obtain ⟨X, ⟨comparison⟩⟩ := existsRepresentation H hH hD
  exact Functor.IsRepresentable.mk'
    (Functor.isoWhiskerRight comparison (forget AddCommGrpCat))

end Criterion

end CategoryTheory.BrownRepresentability.SmallSet

namespace CategoryTheory.Functor.Brown.SmallSet

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [_root_.CategoryTheory.IsTriangulated D]
  [_root_.CategoryTheory.IsTriangulated D'] [HasCoproducts.{w} D]

/-- A triangulated functor preserving coproducts indexed in the universe of a small Brown set
is a left adjoint. -/
@[stacks 0GYH "small-set left-adjoint criterion"]
theorem isLeftAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    F.IsLeftAdjoint := sorry

/-- A triangulated functor preserving coproducts indexed in the universe of a small Brown set
has a right adjoint with its canonical triangulated shift comparison. -/
@[stacks 0GYH "small-set triangulated-right-adjoint criterion"]
theorem hasTriangulatedRightAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end CategoryTheory.Functor.Brown.SmallSet
