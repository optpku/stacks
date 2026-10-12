/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.RelativeModule
import StacksCheckRecall

/-!
# 27.2.2.1 compatibility entry point

The reusable relative module gluing comparison is owned by
`ReasLib.AlgebraicGeometry.Scheme.Gluing.RelativeModule`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

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

/- The reusable comparison is concrete morphism data with the expected source and target. -/
#check
  (AlgebraicGeometry.Scheme.Modules.relativeGlueingComparison
      f ρ 𝓕_U 𝓕_V 𝓕 i_V hVU i_U sourceIdentification thetaURestrict thetaV :
    (pullback ρ).obj 𝓕_U ⟶ 𝓕_V)

/- 27.2.2.1: the relative gluing comparison is the source identification, followed by the
restricted `U`-identification and the inverse `V`-identification. -/
@[stacks 01LJ] #check
  (AlgebraicGeometry.Scheme.Modules.relativeGlueingComparison_def
      f ρ 𝓕_U 𝓕_V 𝓕 i_V hVU i_U sourceIdentification thetaURestrict thetaV :
    AlgebraicGeometry.Scheme.Modules.relativeGlueingComparison
        f ρ 𝓕_U 𝓕_V 𝓕 i_V hVU i_U sourceIdentification thetaURestrict thetaV =
      sourceIdentification.hom ≫ thetaURestrict ≫ thetaV.inv)

end

end AlgebraicGeometry.Scheme.Modules
