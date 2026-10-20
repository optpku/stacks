/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.Comparison
import StacksCheckRecall

/-!
# Syntomic, smooth, étale, and Zariski coverings are fppf coverings

Every syntomic covering family of algebraic spaces over a scheme `S` is an fppf
covering family, and therefore every smooth, étale, or Zariski covering family
is an fppf covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.7.2: any syntomic covering is an fppf covering, and therefore every
smooth, étale, or Zariski covering is an fppf covering. -/
@[stacks 0DFC] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_of_syntomicCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
      (h : SyntomicCovering family),
      FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

@[stacks 0DFC] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_of_smoothCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
      (h : SmoothCovering family),
      FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

@[stacks 0DFC] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_of_etaleCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
      (h : EtaleCovering family),
      FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

@[stacks 0DFC] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_of_zariskiPrecoverage :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      {Xᵢ : ι → AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}
      (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X), FppfCovering Xᵢ f)

#check (AlgebraicGeometry.AlgebraicSpace.fppfCovering_of_mem_etalePrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}
    (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X), FppfCovering Xᵢ f)

end AlgebraicGeometry.AlgebraicSpace
