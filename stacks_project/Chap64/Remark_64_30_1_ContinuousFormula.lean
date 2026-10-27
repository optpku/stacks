/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.AbstractTrace

/-! # Continuous abstract trace formula compatibility -/

public section
universe u

/- Continuous abstract trace laws on specified numerical data. -/
#check (ProfiniteGrp.ContinuousTrace.IsAbstractTraceFormula :
  (S : ProfiniteGrp.DegreeExtension.{u}) → ProfiniteGrp.ContinuousTrace.AbstractTraceData S → Prop)
