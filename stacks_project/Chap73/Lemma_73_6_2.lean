/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic.Comparison

/-!
# Smooth, étale, and Zariski coverings are syntomic coverings

Every smooth covering family of algebraic spaces over a scheme `S` is a syntomic
covering family, and therefore every étale covering family and every Zariski
covering family is a syntomic covering family.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.6.2 (1): any smooth covering is a syntomic covering. -/
@[stacks 0DFB]
#check (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_of_smoothCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X},
    AlgebraicGeometry.AlgebraicSpace.SmoothCovering family →
      AlgebraicGeometry.AlgebraicSpace.SyntomicCovering family)

/- Lemma 73.6.2 (2): any étale covering is a syntomic covering. -/
@[stacks 0DFB]
#check (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_of_etaleCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X},
    AlgebraicGeometry.AlgebraicSpace.EtaleCovering family →
      AlgebraicGeometry.AlgebraicSpace.SyntomicCovering family)

/- Lemma 73.6.2 (3): any Zariski covering is a syntomic covering. -/
@[stacks 0DFB]
#check (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_of_zariskiPrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
    Presieve.ofArrows Xᵢ f ∈ AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage S X →
      AlgebraicGeometry.AlgebraicSpace.SyntomicCovering (fun i ↦ Over.mk (f i)))

/- Companion: an indexed family belonging to the étale precoverage is a syntomic
covering after presentation as an Over family. -/
#check (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_of_mem_etalePrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
    Presieve.ofArrows Xᵢ f ∈ AlgebraicGeometry.AlgebraicSpace.etalePrecoverage X →
      AlgebraicGeometry.AlgebraicSpace.SyntomicCovering (fun i ↦ Over.mk (f i)))

