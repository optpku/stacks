/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Definition_73_5_1_Covering
public import stacks_project.Chap73.Definition_73_6_1_Covering

/-!
# Smooth, étale, and Zariski coverings are syntomic coverings

Every smooth covering family of algebraic spaces over a scheme `S` is a syntomic
covering family, and therefore every étale covering family and every Zariski
covering family is a syntomic covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.6.2 (1): any smooth covering is a syntomic covering. -/
@[stacks 0DFB]
theorem syntomicCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    SmoothCovering family → SyntomicCovering family :=
  sorry

/-- Lemma 73.6.2 (2): any étale covering is a syntomic covering. -/
@[stacks 0DFB]
theorem syntomicCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    EtaleCovering family → SyntomicCovering family :=
  sorry

/-- Lemma 73.6.2 (3): any Zariski covering is a syntomic covering. -/
@[stacks 0DFB]
theorem syntomicCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      SyntomicCovering (fun i ↦ Over.mk (f i)) :=
  sorry

/-- An indexed family that belongs to `etalePrecoverage` is a `SyntomicCovering`
after presentation as an `Over` family. -/
theorem syntomicCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X →
      SyntomicCovering (fun i ↦ Over.mk (f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
