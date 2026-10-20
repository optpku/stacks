/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyAlpha
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Zariski locality of conditions on algebraic spaces

These results state that the listed properties of an algebraic space descend
from an explicit Zariski covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasPropertyAlpha

/-- Property (α) descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyAlpha (𝒰.X i)] : HasPropertyAlpha X :=
  sorry

end HasPropertyAlpha

namespace HasPropertyBeta

/-- Property (β) descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyBeta (𝒰.X i)] : HasPropertyBeta X :=
  sorry

end HasPropertyBeta

namespace IsDecent

/-- Decency descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsDecent (𝒰.X i)] : IsDecent X :=
  sorry

end IsDecent

namespace IsReasonable

/-- Reasonableness descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsReasonable (𝒰.X i)] : IsReasonable X :=
  sorry

end IsReasonable

namespace IsVeryReasonable

/-- Very reasonableness descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsVeryReasonable (𝒰.X i)] : IsVeryReasonable X :=
  sorry

end IsVeryReasonable

namespace IsAbsolutelyZariskiLocallyQuasiSeparated

/-- Absolute Zariski-local quasi-separatedness descends along a Zariski covering. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsAbsolutelyZariskiLocallyQuasiSeparated (𝒰.X i)] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

end IsAbsolutelyZariskiLocallyQuasiSeparated

namespace IsScheme

/-- Being a scheme descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsScheme (𝒰.X i)] : IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
