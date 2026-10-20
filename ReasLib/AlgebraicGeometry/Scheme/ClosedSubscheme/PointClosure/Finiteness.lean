/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Integral
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian

/-!
# Finiteness properties of reduced point closures

This file records local Noetherianity of reduced point closures and quasicompactness of their
canonical inclusions.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- A reduced point closure in a locally Noetherian scheme is locally Noetherian. -/
instance scheme_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    IsLocallyNoetherian (scheme x) :=
  inferInstanceAs (IsLocallyNoetherian (reducedStructure x).ideal.subscheme)

/-- The canonical inclusion of a reduced point closure is quasicompact. -/
instance iota_quasiCompact {X : Scheme.{u}} (x : X) : QuasiCompact (ι x) :=
  inferInstanceAs (QuasiCompact (reducedStructure x).ideal.subschemeι)

end AlgebraicGeometry.Scheme.PointClosure
