/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

/-!
# Comparisons for h covering families of schemes

This module compares h covering families with standard geometric covering
families and valuative covering families.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}

/-- Over a locally Noetherian scheme, h covering families are exactly ph covering families. -/
theorem AlgebraicGeometry.Scheme.hCovering_iff_phCovering
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    {ι : Type v} (family : ι → Over X) :
    AlgebraicGeometry.Scheme.HCovering family ↔
      AlgebraicGeometry.PhCovering
        (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every h covering family is a `V` covering family. -/
theorem AlgebraicGeometry.Scheme.HCovering.isVCovering
    {family : ι → Over T} (hfamily : AlgebraicGeometry.Scheme.HCovering family) :
    AlgebraicGeometry.IsVCovering T
      (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every fppf covering family is an h covering family. -/
theorem AlgebraicGeometry.Scheme.FppfCovering.hCovering
    {family : ι → Over T} (hfamily : AlgebraicGeometry.Scheme.FppfCovering family) :
    AlgebraicGeometry.Scheme.HCovering family := sorry

/-- Every syntomic covering family is an h covering family. -/
theorem AlgebraicGeometry.Scheme.SyntomicCovering.hCovering
    {family : ι → Over T} (hfamily : AlgebraicGeometry.Scheme.SyntomicCovering family) :
    AlgebraicGeometry.Scheme.HCovering family := sorry

/-- Every smooth covering family is an h covering family. -/
theorem AlgebraicGeometry.Scheme.SmoothCovering.hCovering
    {family : ι → Over T} (hfamily : AlgebraicGeometry.Scheme.SmoothCovering family) :
    AlgebraicGeometry.Scheme.HCovering family := sorry

/-- Every family in the étale precoverage is an h covering family. -/
theorem AlgebraicGeometry.Scheme.hCovering_of_mem_etalePrecoverage
    {family : ι → Over T}
    (hfamily : Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      AlgebraicGeometry.Scheme.etalePrecoverage.coverings T) :
    AlgebraicGeometry.Scheme.HCovering family := sorry

/-- Every family in the Zariski precoverage is an h covering family. -/
theorem AlgebraicGeometry.Scheme.hCovering_of_mem_zariskiPrecoverage
    {family : ι → Over T}
    (hfamily : Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      AlgebraicGeometry.Scheme.zariskiPrecoverage.coverings T) :
    AlgebraicGeometry.Scheme.HCovering family := sorry

/-- A bundled fppf cover is canonically an h covering family. -/
theorem AlgebraicGeometry.FppfCover.hCovering
    {T : AlgebraicGeometry.Scheme.{u}} (𝒰 : AlgebraicGeometry.FppfCover.{u, v} T) :
    AlgebraicGeometry.Scheme.HCovering (fun i : 𝒰.I₀ ↦ Over.mk (𝒰.f i)) := sorry
