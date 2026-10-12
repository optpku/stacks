/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction

@[expose] public section

/-!
# Vanishing of Local Cohomology Away from an Ideal

This module gives vanishing criteria for a right adjoint to the inclusion of derived modules
with ideal-power-torsion cohomology.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- If `I` is finitely generated and some `f ∈ I` acts invertibly on a derived `A`-module
`K`, then a right adjoint to the inclusion of derived modules with `I`-power-torsion
cohomology sends `K` to zero. -/
theorem isZero_of_isIso_smul (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) {f : A} (hf : f ∈ I)
    (K : DerivedCategory (ModuleCat A)) [IsIso (f • 𝟙 K)] :
    IsZero (RΓ.obj K) := sorry

/-- If a derived `A`-module comes by restriction of scalars from `A_f`, then a right
adjoint to the inclusion of derived modules with `I`-power-torsion cohomology sends it to
zero whenever `f ∈ I` and `I` is finitely generated. -/
theorem isZero_of_mem_localizationAway_essImage
    (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) {f : A} (hf : f ∈ I)
    {K : DerivedCategory (ModuleCat A)}
    (hK : (ModuleCat.derivedRestrictionOfScalars
      (algebraMap A (Localization.Away f))).essImage K) :
    IsZero (RΓ.obj K) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
