/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Transitivity for relative differentials on schemes

The transitivity projection for relative differentials is expressed using the structural
morphisms of schemes over a tower of base schemes.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.Transitivity

/-- The structural morphism from a scheme to the top of a tower is the composite of the two
successive structural morphisms after passing to morphisms of sheaves. -/
theorem overToShHom_eq_comp (Y Z Z' : Scheme.{u}) [Y.Over Z] [Y.Over Z'] [Z.Over Z']
    [IsOverTower Y Z Z'] :
    (Y ↘ Z').toShHom = (Y ↘ Z).toShHom ≫ (Z ↘ Z').toShHom := sorry

/-- The canonical transitivity projection `Ω[Y/Z'] ⟶ Ω[Y/Z]` for a tower of schemes. -/
noncomputable def projection (Y Z Z' : Scheme.{u})
    [Y.Over Z] [Y.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] :
    Ω[(Y ↘ Z').toShHom] ⟶ Ω[(Y ↘ Z).toShHom] :=
  eqToHom (congrArg (fun f ↦ Ω[f])
      ((congrArg (fun f : Y ⟶ Z' ↦ f.toShHom)
        (comp_over (Y ↘ Z) Z').symm).trans
          ((congrArg (fun f ↦ f.toShHom)
            (Scheme.Hom.comp_toLRSHom (Y ↘ Z) (Z ↘ Z'))).trans
              (LocallyRingedSpace.comp_toShHom
                (Y ↘ Z).toLRSHom (Z ↘ Z').toLRSHom)))) ≫
    RingedSpace.Hom.Differentials.Transitivity.projection
      (Y ↘ Z).toShHom (Z ↘ Z').toShHom

/-- The scheme-level transitivity projection agrees with the ringed-space projection after
transport along the structural-morphism identity. -/
theorem projection_def (Y Z Z' : Scheme.{u})
    [Y.Over Z] [Y.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] :
    projection Y Z Z' =
      eqToHom (congrArg (fun f ↦ Ω[f]) (overToShHom_eq_comp Y Z Z')) ≫
        RingedSpace.Hom.Differentials.Transitivity.projection
          (Y ↘ Z).toShHom (Z ↘ Z').toShHom := sorry

/-- The transitivity projection for relative differentials is an isomorphism when the change
of base is a thickening. -/
instance projection_isIso_of_isThickening (Y Z Z' : Scheme.{u})
    [Y.Over Z] [Y.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] :
    IsIso (projection Y Z Z') := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.Transitivity
