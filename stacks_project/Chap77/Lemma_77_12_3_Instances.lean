module

public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Typeclass instances from a proper flat formal system

The bundled Situation 77.12.1 data already records finite presentation, separatedness,
closed immersions, and proper support. These named instances make those fields available
to typeclass search without unpacking `ProperFlatFormalSystem.of`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The structure morphism of the limit space is separated. -/
instance instSeparated_toBase (S : ProperFlatFormalSystem) : Separated (toBase S.space) :=
  S.toBase_separated

/-- The structure morphism of the limit space is of finite presentation. -/
instance instFinitePresentation_toBase (S : ProperFlatFormalSystem) :
    FinitePresentation (toBase S.space) :=
  S.toBase_finitePresentation

/-- Each finite-stage space maps to the limit space by a closed immersion. -/
instance stageToSpace_isClosedImmersion (S : ProperFlatFormalSystem) (n : ℕ) :
    IsClosedImmersion (S.stageToSpace n) :=
  S.stage_isClosedImmersion n

/-- Each finite-stage module sheaf is of finite presentation. -/
instance moduleSheaf_isFinitePresentation (S : ProperFlatFormalSystem) (n : ℕ) :
    (S.moduleSheaf n).IsFinitePresentation :=
  S.moduleSheaf_finitePresentation n

/-- Each finite-stage module sheaf has proper support over its stage spectrum. -/
instance moduleSheaf_hasProperSupportOver (S : ProperFlatFormalSystem) (n : ℕ) :
    HasProperSupportOver (S.stageToSpec n) (S.moduleSheaf n) :=
  S.moduleSheaf_hasProperSupport n

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
