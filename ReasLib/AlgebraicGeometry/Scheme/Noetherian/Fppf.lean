/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- Local Noetherianity of schemes is local for the fppf precoverage. -/
instance isLocalFppf :
    ObjectProperty.IsLocal
      (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.IsLocallyNoetherian
