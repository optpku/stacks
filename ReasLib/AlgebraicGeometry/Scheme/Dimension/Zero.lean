/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Zero-dimensional schemes

Separation properties of a zero-dimensional scheme are equivalent. Under these conditions,
connected components are points and quasi-compact opens are affine.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.DimensionZero

variable {X : Scheme.{u}}

/-- For a zero-dimensional scheme, quasi-separatedness, separatedness, Hausdorffness, and
closedness of every affine open are equivalent. -/
theorem separation_tfae
    (hXdim : topologicalKrullDim X = 0) :
    List.TFAE [
      QuasiSeparatedSpace X,
      X.IsSeparated,
      T2Space X,
      ∀ U : X.affineOpens, IsClosed (U : Set X)
    ] := sorry

/-- A zero-dimensional scheme is quasi-separated if and only if it is separated. -/
theorem quasiSeparated_iff_isSeparated
    (hXdim : topologicalKrullDim X = 0) :
    QuasiSeparatedSpace X ↔ X.IsSeparated :=
  (separation_tfae hXdim).out 0 1

/-- A zero-dimensional scheme is quasi-separated if and only if its underlying space is
Hausdorff. -/
theorem quasiSeparated_iff_t2Space
    (hXdim : topologicalKrullDim X = 0) :
    QuasiSeparatedSpace X ↔ T2Space X :=
  (separation_tfae hXdim).out 0 2

/-- A zero-dimensional scheme is quasi-separated if and only if every affine open is closed. -/
theorem quasiSeparated_iff_affineOpens_isClosed
    (hXdim : topologicalKrullDim X = 0) :
    QuasiSeparatedSpace X ↔ ∀ U : X.affineOpens, IsClosed (U : Set X) :=
  (separation_tfae hXdim).out 0 3

/-- A quasi-separated zero-dimensional scheme has singleton connected components. -/
theorem totallyDisconnectedSpace
    (hXdim : topologicalKrullDim X = 0) [QuasiSeparatedSpace X] :
    TotallyDisconnectedSpace X := sorry

/-- Every quasi-compact open of a quasi-separated zero-dimensional scheme is affine. -/
theorem isAffineOpen_of_isCompact
    (hXdim : topologicalKrullDim X = 0) [QuasiSeparatedSpace X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) :
    IsAffineOpen U := sorry

/-- A quasi-compact, quasi-separated, zero-dimensional scheme is affine. -/
theorem isAffine_of_compactSpace
    (hXdim : topologicalKrullDim X = 0) [QuasiSeparatedSpace X] [CompactSpace X] :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme.DimensionZero
