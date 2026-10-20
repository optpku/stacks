/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap69.Definition_69_12_1_Instances

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] (F : X.Modules)

/- Lemma 69.12.2: on a locally Noetherian algebraic space, coherence is equivalent to
quasi-coherence and finite type. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType F :
  F.IsCoherent ↔ F.IsQuasicoherent ∧ F.IsFiniteType)
