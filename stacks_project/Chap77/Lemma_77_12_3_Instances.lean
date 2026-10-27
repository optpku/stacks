/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Explicit properties of proper flat formal systems

The stored separatedness, finite presentation, closed-immersion, and proper-support
properties are available through explicit projections.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

#check (toBase_separated : ∀ (S : ProperFlatFormalSystem), Separated (toBase S.space))

#check (toBase_finitePresentation : ∀ (S : ProperFlatFormalSystem),
  FinitePresentation (toBase S.space))

#check (stage_isClosedImmersion : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
  IsClosedImmersion (S.stageToSpace n))

#check (moduleSheaf_finitePresentation : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
  (S.moduleSheaf n).IsFinitePresentation)

#check (moduleSheaf_hasProperSupport : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
  HasProperSupportOver (S.stageToSpec n) (S.moduleSheaf n))

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
