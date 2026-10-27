/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Fppf
import StacksCheckRecall

/-! # Fppf descent for locally quasi-coherent modules with flat base change -/

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
universe u

/- Proposition 103.8.1 (1): an étale module that is locally quasi-coherent
and has flat base change is a sheaf for the fppf topology. -/
@[stacks 0771] #check
  (AlgebraicGeometry.GroupoidsOver.isSheaf_fppf_of_lqcohFbc :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F],
      Presheaf.IsSheaf (fppfRingedSite X).siteTopology
        (etaleModulePresheaf F).presheaf)
