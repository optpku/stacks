/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
public import stacks_project.Chap75.Lemma_75_21_3_Pullback

/-!
# Tensor base-change comparison on algebraic spaces

A map `L(g')^* K ⟶ K'` in `D_QCoh` induces
`L(g')^*(E ⊗^L K) ⟶ L(g')^* E ⊗^L K'` by transporting the fixed-right derived tensor
through the monoidal comparison of `L(g')^*` and applying `𝟙 ⊗ₘ α`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]

/-- The comparison `L(g')^*(E ⊗^L K) ⟶ L(g')^* E ⊗^L K'` associated to
`α : L(g')^* K ⟶ K'`. -/
noncomputable def tensorBaseChangeMap (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal]
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶
      (inclusion X').obj K') :
    (ModuleDerived.pullback g').obj ((inclusion X).obj (tensorObj E K)) ⟶
      (inclusion X').obj (tensorObj (pullbackObj g' E) K') :=
  (ModuleDerived.pullback g').map
      (T_X.objIsoTensor ((inclusion X).obj E) ((inclusion X).obj K)).hom ≫
    (Functor.Monoidal.μIso (ModuleDerived.pullback g')
        ((inclusion X).obj E) ((inclusion X).obj K)).symm.hom ≫
      (𝟙 ((ModuleDerived.pullback g').obj ((inclusion X).obj E)) ⊗ₘ α) ≫
        (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj ((inclusion X).obj E))
          ((inclusion X').obj K')).inv

/-- After forgetting `D_QCoh`, `tensorBaseChangeMap` is the pullback-tensor comparison
followed by `𝟙 ⊗ₘ α`. -/
theorem tensorBaseChangeMap_obj (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal]
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶
      (inclusion X').obj K') :
    tensorBaseChangeMap g' T_X T_X' E K K' α =
      (ModuleDerived.pullback g').map
          (T_X.objIsoTensor ((inclusion X).obj E) ((inclusion X).obj K)).hom ≫
        (Functor.Monoidal.μIso (ModuleDerived.pullback g')
            ((inclusion X).obj E) ((inclusion X).obj K)).symm.hom ≫
          (𝟙 ((ModuleDerived.pullback g').obj ((inclusion X).obj E)) ⊗ₘ α) ≫
            (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj ((inclusion X).obj E))
              ((inclusion X').obj K')).inv :=
  sorry

/-- The source of `tensorBaseChangeMap` has quasi-coherent cohomology. -/
theorem tensorBaseChange_source_mem (g' : X' ⟶ X) (E K : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty X'
      ((ModuleDerived.pullback g').obj ((inclusion X).obj (tensorObj E K))) :=
  sorry

/-- The target of `tensorBaseChangeMap` has quasi-coherent cohomology. -/
theorem tensorBaseChange_target_mem (g' : X' ⟶ X) (E : DerivedQCoh X)
    (K' : DerivedQCoh X') :
    derivedQuasiCoherentModuleProperty X'
      ((inclusion X').obj (tensorObj (pullbackObj g' E) K')) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
