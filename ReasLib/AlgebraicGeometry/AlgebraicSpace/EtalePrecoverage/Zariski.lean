/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion

/-!
# Zariski coverings are étale coverings

Every Zariski covering family of algebraic spaces over a scheme is an étale
covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every Zariski covering family of algebraic spaces over a scheme is an étale
covering family. -/
theorem zariskiPrecoverage_le_etalePrecoverage {S : Scheme.{u}} :
    zariskiPrecoverage S ≤ etalePrecoverage :=
  sorry

/-- An indexed family that belongs to the Zariski precoverage also belongs to the
étale precoverage. -/
theorem ofArrows_mem_etalePrecoverage_of_zariski {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
