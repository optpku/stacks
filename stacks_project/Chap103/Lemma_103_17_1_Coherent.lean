/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_12_2_Coherent
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap103.Lemma_103_17_1_Restrict
public import stacks_project.Chap103.Lemma_103_17_3_Instances

/-!
# Finite presentation of modules on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, finite presentation of an `𝒪_X`-module
is equivalent to quasi-coherence of finite type, and to quasi-coherence together
with coherence of restrictions of pullbacks to locally Noetherian algebraic
spaces (for every such morphism, or for some locally of finite type, flat, and
surjective morphism).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- On a locally Noetherian algebraic stack, an `𝒪_X`-module is of finite
presentation if and only if it is quasi-coherent and of finite type. -/
theorem isFinitePresentation_iff_isQuasicoherent_and_isFiniteType
    (F : SheafOfModules.{u} (structureSheaf X)) :
    F.IsFinitePresentation ↔ F.IsQuasicoherent ∧ F.IsFiniteType :=
  sorry

/-- Finite presentation is equivalent to quasi-coherence together with coherence of
`f^* F |_{U_étale}` for every morphism from a locally Noetherian algebraic space. -/
theorem isFinitePresentation_iff_forall_locallyNoetherian
    (F : SheafOfModules.{u} (structureSheaf X)) :
    F.IsFinitePresentation ↔
      F.IsQuasicoherent ∧
        ∀ (U : AlgebraicSpace S) [AlgebraicSpace.IsLocallyNoetherian U]
          (f : U.toGroupoids ⟶ X),
          ((restrictPullback f).obj F).IsCoherent :=
  sorry

/-- Finite presentation is equivalent to quasi-coherence together with existence of
an algebraic space and a locally of finite type, flat, surjective morphism along
which `f^* F |_{U_étale}` is coherent. -/
theorem isFinitePresentation_iff_exists_locallyOfFiniteType_flat_surjective
    (F : SheafOfModules.{u} (structureSheaf X)) :
    F.IsFinitePresentation ↔
      F.IsQuasicoherent ∧
        ∃ (U : AlgebraicSpace S) (f : U.toGroupoids ⟶ X),
          LocallyOfFiniteType f ∧ Flat f ∧ Surjective f ∧
            ((restrictPullback f).obj F).IsCoherent :=
  sorry

/-- Finite presentation of `F` implies coherence of `f^* F |_{U_étale}` whenever
`U` is a locally Noetherian algebraic space. -/
instance restrictPullback_isCoherent {U : AlgebraicSpace S}
    [AlgebraicSpace.IsLocallyNoetherian U] (f : U.toGroupoids ⟶ X)
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsFinitePresentation] :
    ((restrictPullback f).obj F).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicStack
