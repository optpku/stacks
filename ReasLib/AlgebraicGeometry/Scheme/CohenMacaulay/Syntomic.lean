/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Syntomic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.CohenMacaulay

/-- Cohen–Macaulayness is local for the syntomic precoverage. -/
instance isLocalSyntomic :
    ObjectProperty.IsLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.Scheme.CohenMacaulay
