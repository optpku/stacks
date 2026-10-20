/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.Comparison

/-!
# Comparisons with ph coverings of algebraic spaces

Fppf, syntomic, smooth, étale, and Zariski covering families of algebraic spaces
are ph covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every fppf covering family of algebraic spaces is a ph covering. -/
theorem FppfCovering.phCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : FppfCovering Xi f) : PhCovering Xi f := sorry

/-- An inferred fppf covering family of algebraic spaces is a ph covering. -/
instance FppfCovering.instPhCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    [h : FppfCovering Xi f] : PhCovering Xi f :=
  FppfCovering.phCovering h

/-- Every syntomic covering family of algebraic spaces is a ph covering. -/
theorem phCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) :=
  FppfCovering.phCovering (fppfCovering_of_syntomicCovering h)

/-- Every smooth covering family of algebraic spaces is a ph covering. -/
theorem phCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) :=
  FppfCovering.phCovering (fppfCovering_of_smoothCovering h)

/-- Every étale covering family of algebraic spaces is a ph covering. -/
theorem phCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) :=
  FppfCovering.phCovering (fppfCovering_of_etaleCovering h)

/-- Every displayed Zariski covering family of algebraic spaces is a ph covering. -/
theorem phCovering_of_zariskiPrecoverage {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : Presieve.ofArrows Xi f ∈ zariskiPrecoverage S X) :
    PhCovering Xi f :=
  FppfCovering.phCovering (fppfCovering_of_zariskiPrecoverage h)

/-- The family underlying a bundled fppf covering of an algebraic space is a ph covering. -/
theorem FppfCover.phCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒰 : FppfCover.{u, v} X) : PhCovering 𝒰.X 𝒰.f :=
  FppfCovering.phCovering 𝒰.covering

end AlgebraicGeometry.AlgebraicSpace
