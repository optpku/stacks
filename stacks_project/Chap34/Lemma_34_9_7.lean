/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Comparison

universe u v

/- Lemma 34.9.7: Every fppf covering family is an fpqc covering family. -/
@[stacks 022C] #check (AlgebraicGeometry.Scheme.FppfCovering.fpqcCovering :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {family : ι → CategoryTheory.Over T},
    AlgebraicGeometry.Scheme.FppfCovering family →
      AlgebraicGeometry.Scheme.FpqcCovering family)

#check (AlgebraicGeometry.Scheme.SyntomicCovering.fpqcCovering :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {family : ι → CategoryTheory.Over T},
    AlgebraicGeometry.Scheme.SyntomicCovering family →
      AlgebraicGeometry.Scheme.FpqcCovering family)

#check (AlgebraicGeometry.Scheme.SmoothCovering.fpqcCovering :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {family : ι → CategoryTheory.Over T},
    AlgebraicGeometry.Scheme.SmoothCovering family →
      AlgebraicGeometry.Scheme.FpqcCovering family)

#check (AlgebraicGeometry.Scheme.Cover.fpqcCovering_of_etale :
  ∀ {T : AlgebraicGeometry.Scheme.{u}}
    (cover : AlgebraicGeometry.Scheme.Cover
      AlgebraicGeometry.Scheme.etalePrecoverage T),
    AlgebraicGeometry.Scheme.FpqcCovering
      (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)))

#check (AlgebraicGeometry.Scheme.OpenCover.fpqcCovering :
  ∀ {T : AlgebraicGeometry.Scheme.{u}}
    (cover : AlgebraicGeometry.Scheme.OpenCover T),
    AlgebraicGeometry.Scheme.FpqcCovering
      (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)))
