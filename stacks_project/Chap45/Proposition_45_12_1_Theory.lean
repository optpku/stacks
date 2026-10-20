/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Theory

@[expose] public section

open AlgebraicGeometry.ChernClass

/-! Compatibility surface for the reusable Chern-class theory API. -/
#check AlgebraicGeometry.ChernClass.clopenComplement
#check AlgebraicGeometry.ChernClass.tautologicalPicardClass
#check AlgebraicGeometry.ChernClass.CohomologyTheory
#check AlgebraicGeometry.ChernClass.CohomologyTheory.mk
