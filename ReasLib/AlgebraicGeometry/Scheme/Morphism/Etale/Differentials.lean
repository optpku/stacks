/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X₁ X₂ S₁ S₂ : Scheme.{u}}
variable {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
variable {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}

/-- For a commutative square of schemes whose horizontal morphisms are étale, the canonical
pullback comparison on relative differentials is an isomorphism. -/
instance comparison_isIso_of_etale (sq : CommSq f p₂ p₁ g) [Etale f] [Etale g] :
    IsIso
      (RingedSpace.Hom.Differentials.comparison
        (sq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
