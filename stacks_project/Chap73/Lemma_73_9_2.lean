module

public import stacks_project.Chap73.Definition_73_3_1_Precoverage
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Definition_73_5_1_Covering
public import stacks_project.Chap73.Definition_73_6_1_Covering
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

/-!
# Fppf, syntomic, smooth, étale, and Zariski coverings are fpqc coverings

Every fppf covering family of algebraic spaces over a scheme `S` is an fpqc
covering family, and therefore every syntomic, smooth, étale, or Zariski covering
family is an fpqc covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.9.2 (1): any fppf covering is an fpqc covering. -/
@[stacks 0DFQ]
theorem fpqcCovering_of_fppfCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    (h : FppfCovering Xi f) : FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

/-- Lemma 73.9.2 (2): any syntomic covering is an fpqc covering. -/
@[stacks 0DFQ]
theorem fpqcCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    FpqcCovering family := sorry

/-- Lemma 73.9.2 (3): any smooth covering is an fpqc covering. -/
@[stacks 0DFQ]
theorem fpqcCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    FpqcCovering family := sorry

/-- Lemma 73.9.2 (4): any étale covering is an fpqc covering. -/
@[stacks 0DFQ]
theorem fpqcCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    FpqcCovering family := sorry

/-- Lemma 73.9.2 (5): any Zariski covering is an fpqc covering. -/
@[stacks 0DFQ]
theorem fpqcCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X) :
    FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

/-- An indexed family that belongs to `etalePrecoverage` is an `FpqcCovering`
after presentation as an `Over` family. -/
theorem fpqcCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X) :
    FpqcCovering (fun i ↦ Over.mk (f i)) := sorry

end AlgebraicGeometry.AlgebraicSpace
