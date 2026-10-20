/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Comparisons with syntomic coverings of algebraic spaces

Smooth, étale, and Zariski covering families of algebraic spaces are syntomic
covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every smooth covering family of algebraic spaces is a syntomic covering. -/
theorem syntomicCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    SmoothCovering family → SyntomicCovering family :=
  sorry

/-- Every étale covering family of algebraic spaces is a syntomic covering. -/
theorem syntomicCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    EtaleCovering family → SyntomicCovering family :=
  sorry

/-- Every displayed Zariski covering family of algebraic spaces is a syntomic
covering. -/
theorem syntomicCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      SyntomicCovering (fun i ↦ Over.mk (f i)) :=
  sorry

/-- Every displayed family in the étale precoverage is a syntomic covering after
presentation as an Over family. -/
theorem syntomicCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X →
      SyntomicCovering (fun i ↦ Over.mk (f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

