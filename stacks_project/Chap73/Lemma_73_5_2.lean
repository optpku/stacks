module

public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Definition_73_5_1_Covering

/-!
# Étale and Zariski coverings are smooth coverings

Every étale covering family of algebraic spaces over a scheme `S` is a smooth
covering family, and therefore every Zariski covering family is a smooth covering
family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.5.2 (1): any étale covering is a smooth covering. -/
@[stacks 0DFA]
theorem smoothCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    EtaleCovering family → SmoothCovering family :=
  sorry

/-- Lemma 73.5.2 (2): any Zariski covering is a smooth covering. -/
@[stacks 0DFA]
theorem smoothCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      SmoothCovering (fun i ↦ Over.mk (f i)) :=
  sorry

/-- An indexed family that belongs to `etalePrecoverage` is a `SmoothCovering`
after presentation as an `Over` family. -/
theorem smoothCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X →
      SmoothCovering (fun i ↦ Over.mk (f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
