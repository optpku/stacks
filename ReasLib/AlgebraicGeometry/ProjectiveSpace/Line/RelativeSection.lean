/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-!
# Sections of the relative projective line

This file defines the zero and infinity sections of the projective line over an arbitrary
scheme and records their structure-map equations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.Relative

/-- The integral zero section is compatible with the maps to the terminal scheme. -/
theorem zeroSection_fac (S : Scheme.{u}) :
    𝟙 S ≫ terminal.from S =
      (specULiftZIsTerminal.from S ≫ ProjectiveLine.zeroSection (ULift.{u} ℤ)) ≫
        terminal.from (ProjectiveLine.scheme (ULift.{u} ℤ)) := sorry

/-- The zero section `[1 : 0]` of the relative projective line `ℙ¹ₛ`. -/
noncomputable def zeroSection (S : Scheme.{u}) : S ⟶ ProjectiveSpace 1 S :=
  pullback.lift (𝟙 S)
    (specULiftZIsTerminal.from S ≫ ProjectiveLine.zeroSection (ULift.{u} ℤ))
      (zeroSection_fac S)

/-- The relative zero section is a section of the projection to `S`. -/
theorem zeroSection_toBase (S : Scheme.{u}) :
    zeroSection S ≫ ProjectiveSpace.toBase 1 S = 𝟙 S := sorry

/-- The integral infinity section is compatible with the maps to the terminal scheme. -/
theorem infinitySection_fac (S : Scheme.{u}) :
    𝟙 S ≫ terminal.from S =
      (specULiftZIsTerminal.from S ≫ ProjectiveLine.infinitySection (ULift.{u} ℤ)) ≫
        terminal.from (ProjectiveLine.scheme (ULift.{u} ℤ)) := sorry

/-- The infinity section `[0 : 1]` of the relative projective line `ℙ¹ₛ`. -/
noncomputable def infinitySection (S : Scheme.{u}) : S ⟶ ProjectiveSpace 1 S :=
  pullback.lift (𝟙 S)
    (specULiftZIsTerminal.from S ≫ ProjectiveLine.infinitySection (ULift.{u} ℤ))
      (infinitySection_fac S)

/-- The relative infinity section is a section of the projection to `S`. -/
theorem infinitySection_toBase (S : Scheme.{u}) :
    infinitySection S ≫ ProjectiveSpace.toBase 1 S = 𝟙 S := sorry

end AlgebraicGeometry.ProjectiveLine.Relative
