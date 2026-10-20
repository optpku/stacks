/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal

/-!
# Affine diagonal from the resolution property
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact and quasi-separated scheme with the resolution property has affine absolute
diagonal. -/
theorem affineDiagonal_of_hasResolutionProperty {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X) :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) := sorry

end AlgebraicGeometry.Scheme
