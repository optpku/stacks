/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.HomCohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.71.5

@stack 00LT
-/

@[stacks 00LT "(1), independence of the compatible lift"]
#check @ChainComplex.IsFreeResolution.homologyMap_eq_of_compatibleLifts

@[stacks 00LT "(2), isomorphism induced by a lifted isomorphism"]
#check @ChainComplex.IsFreeResolution.homologyMap_isIso_of_isIso

@[stacks 00LT "(3), identity induced by an identity lift"]
#check @ChainComplex.IsFreeResolution.homologyMap_eq_id

/- Reusable lift and induced-map objects behind the three source clauses. -/
#check @CategoryTheory.ProjectiveResolution.Hom.id
#check @CategoryTheory.ProjectiveResolution.Hom.comp
#check @CategoryTheory.ProjectiveResolution.Hom.lift
#check @ChainComplex.IsFreeResolution.homologyMap
