/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone
import StacksCheckRecall

@[expose] public section

/-!
# Definition 24.22.2

The textbook cone of a morphism of differential graded module sheaves is the neutral
`DifferentialGradedModule.mappingCone`. Its object, degreewise, differential, and
cochain-complex comparison APIs are recalled here without a chapter-owned duplicate.
-/

open SheafOfModules.RingedSite

@[stacks 0FS5] #check @DifferentialGradedModule.mappingCone
@[stacks 0FS5] #check @DifferentialGradedModule.mappingCone_X
@[stacks 0FS5] #check @DifferentialGradedModule.mappingCone_apply
@[stacks 0FS5] #check @DifferentialGradedModule.mappingCone_d
@[stacks 0FS5] #check @DifferentialGradedModule.mappingConeXIsoCochainMappingCone
@[stacks 0FS5] #check @DifferentialGradedModule.mappingConeToCochainMappingCone
