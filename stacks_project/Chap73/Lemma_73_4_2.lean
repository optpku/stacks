/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_3_1_Precoverage
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Zariski coverings are étale coverings

Every Zariski covering family of algebraic spaces over a scheme `S` is an
étale covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.4.2: any Zariski covering is an étale covering. -/
@[stacks 0DF1]
theorem zariskiPrecoverage_le_etalePrecoverage {S : Scheme.{u}} :
    zariskiPrecoverage S ≤ etalePrecoverage :=
  sorry

/-- An indexed family that belongs to `zariskiPrecoverage` also belongs to
`etalePrecoverage`. -/
theorem ofArrows_mem_etalePrecoverage_of_zariski {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
