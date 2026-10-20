/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every étale covering family of schemes is a smooth covering family. -/
theorem etalePrecoverage_le_bigSmoothPrecoverage :
    etalePrecoverage.{u} ≤ bigSmoothPrecoverage.{u} := sorry

/-- Every Zariski covering family of schemes is a smooth covering family. -/
theorem zariskiPrecoverage_le_bigSmoothPrecoverage :
    zariskiPrecoverage.{u} ≤ bigSmoothPrecoverage.{u} := sorry

end AlgebraicGeometry.Scheme
