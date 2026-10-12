/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative module gluing comparisons

This leaf owns the explicit comparison morphism that occurs when a module on a
scheme over a base is identified locally with modules on a pair of nested open
subschemes of the base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {S X X_U X_V : Scheme.{u}} {V : S.Opens}
variable (f : X ⟶ S) (ρ : X_V ⟶ X_U)
variable (𝓕_U : X_U.Modules) (𝓕_V : X_V.Modules) (𝓕 : X.Modules)
variable (i_V : (f ⁻¹ᵁ V).toScheme ≅ X_V)
variable {U : S.Opens} (hVU : V ≤ U)
variable (i_U : (f ⁻¹ᵁ U).toScheme ≅ X_U)
variable (sourceIdentification :
  (pullback ρ).obj 𝓕_U ≅
    (pullback i_V.inv).obj
      (((pullback i_U.hom).obj 𝓕_U).restrict (X.homOfLE (f.preimage_mono hVU))))
variable (thetaURestrict :
  (pullback i_V.inv).obj
      (((pullback i_U.hom).obj 𝓕_U).restrict (X.homOfLE (f.preimage_mono hVU))) ⟶
    (pullback i_V.inv).obj (𝓕.restrict (f ⁻¹ᵁ V).ι))
variable (thetaV :
  𝓕_V ≅ (pullback i_V.inv).obj (𝓕.restrict (f ⁻¹ᵁ V).ι))

/-- After identifying the pullback of the module over the larger open with its restriction to the
smaller open, the relative gluing comparison is the restriction comparison followed by the inverse
local identification over the smaller open. -/
@[stacks 01LJ]
def relativeGlueingComparison : (pullback ρ).obj 𝓕_U ⟶ 𝓕_V :=
  sourceIdentification.hom ≫ thetaURestrict ≫ thetaV.inv

/-- The relative gluing comparison unfolds to its three displayed factors. -/
@[stacks 01LJ]
theorem relativeGlueingComparison_def :
    relativeGlueingComparison f ρ 𝓕_U 𝓕_V 𝓕 i_V hVU i_U sourceIdentification thetaURestrict
        thetaV =
      sourceIdentification.hom ≫ thetaURestrict ≫ thetaV.inv := rfl

end

end AlgebraicGeometry.Scheme.Modules
