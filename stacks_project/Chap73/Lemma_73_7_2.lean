module

public import stacks_project.Chap73.Definition_73_3_1_Precoverage
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Definition_73_5_1_Covering
public import stacks_project.Chap73.Definition_73_6_1_Covering
public import stacks_project.Chap73.Definition_73_7_1_FppfCover

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

/-- Lemma 73.7.2 (1): any syntomic covering is an fppf covering. -/
@[stacks 0DFC]
theorem fppfCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.7.2 (2): any smooth covering is an fppf covering. -/
@[stacks 0DFC]
theorem fppfCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.7.2 (3): any étale covering is an fppf covering. -/
@[stacks 0DFC]
theorem fppfCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 73.7.2 (4): any Zariski covering is an fppf covering. -/
@[stacks 0DFC]
theorem fppfCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X) :
    FppfCovering Xᵢ f := sorry

/-- An indexed family that belongs to `etalePrecoverage` is an `FppfCovering`. -/
theorem fppfCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X) :
    FppfCovering Xᵢ f := sorry

end AlgebraicGeometry.AlgebraicSpace
