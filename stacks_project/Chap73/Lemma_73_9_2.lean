/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Comparison
import StacksCheckRecall

/-!
# Fppf, syntomic, smooth, étale, and Zariski coverings are fpqc coverings

Every fppf covering family of algebraic spaces over a scheme `S` is an fpqc
covering family, and therefore every syntomic, smooth, étale, or Zariski covering
family is an fpqc covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.9.2. Any fppf covering is an fpqc covering, and hence every
syntomic, smooth, étale, or Zariski covering is an fpqc covering. -/
@[stacks 0DFQ]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_fppfCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : FppfCovering Xi f), FpqcCovering (fun i ↦ Over.mk (f i)))

/- Lemma 73.9.2 (2): any syntomic covering is an fpqc covering. -/
@[stacks 0DFQ]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_syntomicCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family),
    FpqcCovering family)

/- Lemma 73.9.2 (3): any smooth covering is an fpqc covering. -/
@[stacks 0DFQ]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_smoothCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family),
    FpqcCovering family)

/- Lemma 73.9.2 (4): any étale covering is an fpqc covering. -/
@[stacks 0DFQ]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_etaleCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family),
    FpqcCovering family)

/- Lemma 73.9.2 (5): any Zariski covering is an fpqc covering. -/
@[stacks 0DFQ]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_zariskiPrecoverage :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X),
    FpqcCovering (fun i ↦ Over.mk (f i)))

/- An indexed family that belongs to `etalePrecoverage` is an `FpqcCovering`
after presentation as an `Over` family. -/
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_of_mem_etalePrecoverage :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X),
    FpqcCovering (fun i ↦ Over.mk (f i)))
