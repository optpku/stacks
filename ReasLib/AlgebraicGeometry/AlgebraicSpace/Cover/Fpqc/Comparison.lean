/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.Comparison

/-!
# Comparisons with fpqc coverings of algebraic spaces

Fppf, syntomic, smooth, étale, and Zariski covering families of algebraic spaces
are fpqc covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every fppf covering family of algebraic spaces is an fpqc covering. -/
theorem fpqcCovering_of_fppfCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : FppfCovering Xi f) : FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

/-- Every syntomic covering family of algebraic spaces is an fpqc covering. -/
theorem fpqcCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    FpqcCovering family := sorry

/-- Every smooth covering family of algebraic spaces is an fpqc covering. -/
theorem fpqcCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    FpqcCovering family := sorry

/-- Every étale covering family of algebraic spaces is an fpqc covering. -/
theorem fpqcCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    FpqcCovering family := sorry

/-- Every displayed Zariski covering family of algebraic spaces is an fpqc covering. -/
theorem fpqcCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X) :
    FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

/-- Every displayed family in the étale precoverage is an fpqc covering after
presentation as an `Over` family. -/
theorem fpqcCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X) :
    FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

end AlgebraicGeometry.AlgebraicSpace
