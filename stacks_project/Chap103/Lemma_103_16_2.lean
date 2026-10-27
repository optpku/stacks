/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
public import stacks_project.Chap103.Lemma_103_16_1
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.LowerShriek
import StacksCheckRecall

/-!
# Quasi-coherence of module lower shriek

On an algebraic stack, module lower shriek along the lisse-étale and
flat-fppf inclusions preserves quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory

noncomputable section

universe u

/- Lemma 103.16.2 (1): module lower shriek from the lisse-étale site of an
algebraic stack preserves quasi-coherent modules. -/
@[stacks 07B0] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.obj_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) [H.IsQuasicoherent],
      ((lisseEtaleModuleLowerShriek X).obj H).IsQuasicoherent)

/- Lemma 103.16.2 (2): module lower shriek from the flat-fppf site of an
algebraic stack preserves quasi-coherent modules. -/
@[stacks 07B0] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.obj_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) [H.IsQuasicoherent],
      ((flatFppfModuleLowerShriek X).obj H).IsQuasicoherent)
