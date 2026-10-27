/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap77.Lemma_77_12_5_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Concentration

/-! # Restricted degree-zero cohomology of a formal-system homotopy limit -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.restrictDegreeZero :
    ∀ (S : ProperFlatFormalSystem.{u})
      [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
      (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
      (W : OpenSubspace S.space), W.X.Modules)
