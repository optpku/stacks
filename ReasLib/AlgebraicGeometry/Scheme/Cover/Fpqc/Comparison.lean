/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

/-!
# Comparisons with fpqc covering families

The standard geometric covering families considered here are all fpqc
covering families.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}

/-- Every fppf-covering indexed family of schemes is fpqc-covering. -/
theorem AlgebraicGeometry.Scheme.FppfCovering.fpqcCovering
    {family : ι → CategoryTheory.Over T}
    (hfamily : AlgebraicGeometry.Scheme.FppfCovering family) :
    AlgebraicGeometry.Scheme.FpqcCovering family := sorry

/-- Every syntomic-covering indexed family of schemes is fpqc-covering. -/
theorem AlgebraicGeometry.Scheme.SyntomicCovering.fpqcCovering
    {family : ι → CategoryTheory.Over T}
    (hfamily : AlgebraicGeometry.Scheme.SyntomicCovering family) :
    AlgebraicGeometry.Scheme.FpqcCovering family := sorry

/-- Every smooth-covering indexed family of schemes is fpqc-covering. -/
theorem AlgebraicGeometry.Scheme.SmoothCovering.fpqcCovering
    {family : ι → CategoryTheory.Over T}
    (hfamily : AlgebraicGeometry.Scheme.SmoothCovering family) :
    AlgebraicGeometry.Scheme.FpqcCovering family := sorry

/-- An étale cover of a scheme is fpqc-covering as an indexed family in the
slice category. -/
theorem AlgebraicGeometry.Scheme.Cover.fpqcCovering_of_etale
    (cover : AlgebraicGeometry.Scheme.Cover
      AlgebraicGeometry.Scheme.etalePrecoverage T) :
    AlgebraicGeometry.Scheme.FpqcCovering
      (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)) := sorry

/-- A Zariski open cover of a scheme is fpqc-covering as an indexed family in
the slice category. -/
theorem AlgebraicGeometry.Scheme.OpenCover.fpqcCovering
    (cover : AlgebraicGeometry.Scheme.OpenCover T) :
    AlgebraicGeometry.Scheme.FpqcCovering
      (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)) := sorry
