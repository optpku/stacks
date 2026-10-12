/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_8_1_PhCovering
public import stacks_project.Chap73.Lemma_73_7_2

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

/-- Lemma 73.8.2 (1): any fppf covering is a ph covering. -/
@[stacks 0DFH]
theorem FppfCovering.phCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : FppfCovering Xi f) : PhCovering Xi f := sorry

/-- Lemma 73.8.2 (2): any syntomic covering is a ph covering. -/
@[stacks 0DFH]
theorem phCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.8.2 (3): any smooth covering is a ph covering. -/
@[stacks 0DFH]
theorem phCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.8.2 (4): any étale covering is a ph covering. -/
@[stacks 0DFH]
theorem phCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.8.2 (5): any Zariski covering is a ph covering. -/
@[stacks 0DFH]
theorem phCovering_of_zariskiPrecoverage {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : Presieve.ofArrows Xi f ∈ zariskiPrecoverage S X) :
    PhCovering Xi f := sorry

/-- A bundled fppf covering of an algebraic space is a ph covering family. -/
theorem FppfCover.phCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒰 : FppfCover X) : PhCovering 𝒰.X 𝒰.f := sorry

end AlgebraicGeometry.AlgebraicSpace
