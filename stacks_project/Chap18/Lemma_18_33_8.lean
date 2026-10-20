/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Lemma 18.33.8: a locally surjective map of ring sheaves has the canonical exact conormal
sequence, whose final morphism is epic. The site-generic data and conclusions are ReasLib API. -/
@[stacks 08TS]
#check @conormalSequence_exact

#check @conormalIdeal
#check @sectionConormalMap
#check @conormalSource
#check @conormalTensorTerm
#check @conormalMap
#check @conormalToDifferentials
#check @conormalToDifferentials_adj
#check @conormal_comp_zero
#check @conormalSequence
#check @conormalToDifferentials_epi
#check @conormalSequence_exact_of_sectionwiseSurjective
#check @conormalToDifferentials_epi_of_sectionwiseSurjective
#check @sectionConormalMap_toCotangent
