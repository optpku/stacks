/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.ResolutionProperty

/-!
# Resolution property of regular schemes

A quasi-compact regular scheme with affine diagonal has the resolution property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact regular scheme with affine diagonal has the resolution property. -/
theorem hasResolutionProperty_of_compact_regular_affineDiagonal {X : Scheme.{u}}
    [CompactSpace X] [Regular X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    HasResolutionProperty X := sorry

end AlgebraicGeometry.Scheme
