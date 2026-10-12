/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.RelativeSection
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily

/-!
# Sections of projective-line families

This file defines the structure morphism and the canonical zero and infinity sections of
`X ×ₛ ℙ¹ₛ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The structure morphism from `X ×ₛ ℙ¹ₛ` to `S`. -/
abbrev toBase {S : Scheme.{u}} (X : Over S) : space X ⟶ S :=
  pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom

/-- The family structure morphism is the first projection followed by `X ⟶ S`. -/
theorem toBase_def {S : Scheme.{u}} (X : Over S) :
    toBase X = pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom := sorry

/-- The identity of `X` and the relative zero section have compatible maps to `S`. -/
theorem zeroSection_fac {S : Scheme.{u}} (X : Over S) :
    𝟙 X.left ≫ X.hom =
      (X.hom ≫ ProjectiveLine.Relative.zeroSection S) ≫
        ProjectiveSpace.toBase 1 S := sorry

/-- The canonical zero-section morphism `i₀ : X ⟶ X ×ₛ ℙ¹ₛ`. -/
noncomputable def zeroSection {S : Scheme.{u}} (X : Over S) : X.left ⟶ space X :=
  pullback.lift (𝟙 X.left) (X.hom ≫ ProjectiveLine.Relative.zeroSection S)
    (zeroSection_fac X)

/-- The zero section projects to the identity on `X`. -/
theorem zeroSection_fst {S : Scheme.{u}} (X : Over S) :
    zeroSection X ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) = 𝟙 X.left := sorry

/-- The second projection of the zero section is the relative zero section. -/
theorem zeroSection_snd {S : Scheme.{u}} (X : Over S) :
    zeroSection X ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) =
      X.hom ≫ ProjectiveLine.Relative.zeroSection S := sorry

/-- The canonical zero section of a projective-line family is a closed immersion. -/
instance instIsClosedImmersionZeroSection {S : Scheme.{u}} (X : Over S) :
    IsClosedImmersion (zeroSection X) := sorry

/-- The identity of `X` and the relative infinity section have compatible maps to `S`. -/
theorem infinitySection_fac {S : Scheme.{u}} (X : Over S) :
    𝟙 X.left ≫ X.hom =
      (X.hom ≫ ProjectiveLine.Relative.infinitySection S) ≫
        ProjectiveSpace.toBase 1 S := sorry

/-- The canonical infinity-section morphism `i∞ : X ⟶ X ×ₛ ℙ¹ₛ`. -/
noncomputable def infinitySection {S : Scheme.{u}} (X : Over S) : X.left ⟶ space X :=
  pullback.lift (𝟙 X.left) (X.hom ≫ ProjectiveLine.Relative.infinitySection S)
    (infinitySection_fac X)

/-- The infinity section projects to the identity on `X`. -/
theorem infinitySection_fst {S : Scheme.{u}} (X : Over S) :
    infinitySection X ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) = 𝟙 X.left := sorry

/-- The second projection of the infinity section is the relative infinity section. -/
theorem infinitySection_snd {S : Scheme.{u}} (X : Over S) :
    infinitySection X ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) =
      X.hom ≫ ProjectiveLine.Relative.infinitySection S := sorry

/-- The canonical infinity section of a projective-line family is a closed immersion. -/
instance instIsClosedImmersionInfinitySection {S : Scheme.{u}} (X : Over S) :
    IsClosedImmersion (infinitySection X) := sorry

end AlgebraicGeometry.ProjectiveLineFamily
