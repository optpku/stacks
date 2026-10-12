/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Pullback

/-!
# Actual tensor-power maps on fixed-degree projective opens

The map is iterated multiplication of homogeneous fractions. Invertibility is
asserted only after restriction to the open covered by degree-d basic opens.
No global invertibility or generation-in-degree-one assumption is made.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u v

namespace AlgebraicGeometry.Proj.AssociatedModule.CanonicalAlgebra

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- Iterated actual multiplication, with only arithmetic degree transports. -/
def powerHom (d : ℤ) : (n : ℕ) →
    (RingedSpace.TensorPower.sheaf (twistingSheaf 𝒜 d) n ⟶
      twistingSheaf 𝒜 ((n : ℤ) * d)) :=
  Nat.rec
    (unitHom 𝒜 ≫ eqToHom (congrArg (twistingSheaf 𝒜) (Int.zero_mul d).symm))
    (fun n f ↦ (𝟙 _ ⊗ₘ f) ≫ mulHom 𝒜 d ((n : ℤ) * d) ≫
      eqToHom (congrArg (twistingSheaf 𝒜) (by simp [add_mul, add_comm] :
        d + (n : ℤ) * d = ((n + 1 : ℕ) : ℤ) * d)))

/-- The line module is the restriction of the actual degree-d Serre sheaf. -/
def degreeLine (d : ℕ) : (degreeOpen 𝒜 d).toScheme.Modules :=
  (Scheme.Modules.pullback (degreeOpen 𝒜 d).ι).obj (twistingSheaf 𝒜 (d : ℤ))

/-- On degree-d basic opens, multiplication by their invertible homogeneous
denominator trivializes this particular twist. -/
theorem degreeLine_invertible {d : ℕ} (hd : 0 < d) :
    Scheme.Modules.Invertible (degreeLine 𝒜 d) := sorry

/-- The local tensor-power map is restriction of the displayed multiplication map. -/
def degreePowerHom (d n : ℕ) :
    RingedSpace.TensorPower.sheaf (degreeLine 𝒜 d) n ⟶
      (Scheme.Modules.pullback (degreeOpen 𝒜 d).ι).obj
        (twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))) :=
  (RelativeProjDegreeQuadruple.pullbackTensorPowerIsoOf (degreeOpen 𝒜 d).ι
    (RelativeProjDegreeQuadruple.canonicalPullbackCore (degreeOpen 𝒜 d).ι)
    (twistingSheaf 𝒜 (d : ℤ)) n).inv ≫
    (Scheme.Modules.pullback (degreeOpen 𝒜 d).ι).map (powerHom 𝒜 (d : ℤ) n)

/-- Localization at a degree-d element makes precisely these maps invertible. -/
theorem degreePowerHom_isIso {d : ℕ} (hd : 0 < d) (n : ℕ) :
    IsIso (degreePowerHom 𝒜 d n) := sorry

/-- Invert the fixed multiplication map on the fixed degree open. -/
def degreePowerIso {d : ℕ} (hd : 0 < d) (n : ℕ) :
    RingedSpace.TensorPower.sheaf (degreeLine 𝒜 d) n ≅
      (Scheme.Modules.pullback (degreeOpen 𝒜 d).ι).obj
        (twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))) :=
  @asIso _ _ _ _ (degreePowerHom 𝒜 d n) (degreePowerHom_isIso 𝒜 hd n)

end AlgebraicGeometry.Proj.AssociatedModule.CanonicalAlgebra
