/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Zero
import StacksCheckRecall

@[expose] public section

universe u

/-
Lemma 28.10.6: Let `X` be a scheme of dimension zero. Then quasi-separatedness, separatedness,
Hausdorffness, and closedness of every affine open are equivalent. In this case the connected
components of `X` are points and every quasi-compact open of `X` is affine. In particular, a
quasi-compact `X` is affine.
-/
@[stacks 0CKV] #check
  (AlgebraicGeometry.Scheme.DimensionZero.separation_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0),
      List.TFAE [
        QuasiSeparatedSpace X,
        X.IsSeparated,
        T2Space X,
        ∀ U : X.affineOpens, IsClosed (U : Set X)
      ])

#check
  (AlgebraicGeometry.Scheme.DimensionZero.quasiSeparated_iff_isSeparated :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0),
      QuasiSeparatedSpace X ↔ X.IsSeparated)

#check
  (AlgebraicGeometry.Scheme.DimensionZero.quasiSeparated_iff_t2Space :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0),
      QuasiSeparatedSpace X ↔ T2Space X)

#check
  (AlgebraicGeometry.Scheme.DimensionZero.quasiSeparated_iff_affineOpens_isClosed :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0),
      QuasiSeparatedSpace X ↔ ∀ U : X.affineOpens, IsClosed (U : Set X))

#check
  (AlgebraicGeometry.Scheme.DimensionZero.totallyDisconnectedSpace :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0)
      [QuasiSeparatedSpace X],
        TotallyDisconnectedSpace X)

#check
  (AlgebraicGeometry.Scheme.DimensionZero.isAffineOpen_of_isCompact :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0)
      [QuasiSeparatedSpace X] {U : X.Opens},
        IsCompact (U : Set X) → AlgebraicGeometry.IsAffineOpen U)

#check
  (AlgebraicGeometry.Scheme.DimensionZero.isAffine_of_compactSpace :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (hXdim : topologicalKrullDim X = 0)
      [QuasiSeparatedSpace X] [CompactSpace X],
        AlgebraicGeometry.IsAffine X)
