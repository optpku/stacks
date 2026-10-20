/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph.Comparison
import StacksCheckRecall

/-!
# Fppf coverings of algebraic spaces are ph coverings

Every fppf covering family of algebraic spaces over a scheme `S` is a ph
covering family, and therefore every syntomic, smooth, étale, or Zariski
covering family is a ph covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.8.2: any fppf covering is a ph covering, and therefore every syntomic,
smooth, étale, or Zariski covering is a ph covering. -/
@[stacks 0DFH] #check
  (AlgebraicGeometry.AlgebraicSpace.FppfCovering.phCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
      (h : FppfCovering Xi f), PhCovering Xi f)

#check (AlgebraicGeometry.AlgebraicSpace.phCovering_of_syntomicCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
    (h : SyntomicCovering family),
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

#check (AlgebraicGeometry.AlgebraicSpace.phCovering_of_smoothCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
    (h : SmoothCovering family),
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

#check (AlgebraicGeometry.AlgebraicSpace.phCovering_of_etaleCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {family : ι → Over X}
    (h : EtaleCovering family),
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

#check (AlgebraicGeometry.AlgebraicSpace.phCovering_of_zariskiPrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : Presieve.ofArrows Xi f ∈ zariskiPrecoverage S X), PhCovering Xi f)

#check (AlgebraicGeometry.AlgebraicSpace.FppfCover.phCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : FppfCover.{u, v} X),
    PhCovering 𝒰.X 𝒰.f)

end AlgebraicGeometry.AlgebraicSpace
