/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.ProjectiveBundle

@[expose] public section

open AlgebraicGeometry.ChernClass

/-! Compatibility checks for the projective-bundle Chern API. -/
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.ofProjectiveBundleFormula
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.tautologicalFirstChernClass
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.tautologicalFirstChernClass_def
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.signedChernCoordinates
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.projectiveBundleEquiv_signedChernCoordinates
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.chernClass
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.chernClass_zero
#check @AlgebraicGeometry.ChernClass.ProjectiveBundleContext.chernClass_relation
