/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.PseudoTorsor

/-!
# Infinitesimal deformations with identity target thickening

When the target thickening is the identity, the prescribed conormal map vanishes and the
compatible local deformations are precisely the morphisms restricting to the original map.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y : Scheme.{u}}

/-- A conormal map into a first-order thickening vanishes when its source comes from the
identity morphism of the target. -/
theorem conormalMap_id_eq_zero (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [IsFirstOrderThickening i]
    [i.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf (𝟙 Y)) ⟶
      Scheme.Hom.conormalSheaf i) :
    A = 0 := sorry

/-- For an identity target thickening, compatible local deformations are exactly the
base-preserving morphisms whose restriction along the source thickening is the original map. -/
theorem sections_id (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [IsFirstOrderThickening i]
    [i.IsOver S] [a.IsOver S] (U' : X'.Opens) :
    sections S i (𝟙 Y) a 0 U' =
      {a' : U'.toScheme ⟶ Y |
        a' ≫ (Y ↘ S) = U'.ι ≫ (X' ↘ S) ∧
          (i ∣_ U') ≫ a' = (i ⁻¹ᵁ U').ι ≫ a} := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
