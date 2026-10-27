/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Finite
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.IdealPowerTorsion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- At finite algebraization distance `n`, the completed local data satisfy the local
algebraization-situation condition with parameter `s - n`. -/
def HasAlgebraizationSituationAtDistance (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    [hmon : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u}
        (completedLocalRing S (closedFiberOpenPoint S y hy))))]
    (C : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      CategoryTheory.DerivedCategory.CanonicalClosedPresentation
        (A := completedLocalRing S (closedFiberOpenPoint S y hy)))
    (s d : ℤ) : Prop :=
  ∀ y : S.Y, (hy : S.y y ∈ S.U) →
    ∀ n : ℕ, algebraizationDistance S y = n →
      @Ideal.LocalCohomology.AlgebraizationSituation
        (completedLocalRing S (closedFiberOpenPoint S y hy)) _ _ (hmon y hy) (C y hy)
        (completedIdeal S (closedFiberOpenPoint S y hy))
        (completedStalk S F (closedFiberOpenPoint S y hy)).carrier _ _
        (completedStalk_finite S F (closedFiberOpenPoint S y hy))
        {q | q.asIdeal = completedMaximalIdeal S (closedFiberOpenPoint S y hy)}
        (s - (n : ℤ)) d

/-- Ideal-power annihilation forces every ordinary depth and dimension inequality. -/
theorem inequalities_of_isAnnihilatedByIdealPower (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ)
    (hF : IsAnnihilatedByIdealPowerOnAffineOpens
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) F) :
    SatisfiesInequalities S F a b := sorry

/-- Ordinary `(a + 1, b)` inequalities imply strict `(a, b)` inequalities. -/
theorem strictInequalities_of_inequalities_add_one (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ)
    (hF : SatisfiesInequalities S F (a + 1) b) :
    SatisfiesStrictInequalities S F a b := sorry

/-- Under the cohomological-dimension and dualizing hypotheses, ordinary `(s, s + d)`
inequalities are equivalent to the completed local algebraization situations. -/
theorem inequalities_iff_algebraizationSituation (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    [hmonA : MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u} A))]
    (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
    [hmon : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u}
        (completedLocalRing S (closedFiberOpenPoint S y hy))))]
    (Clocal : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      CategoryTheory.DerivedCategory.CanonicalClosedPresentation
        (A := completedLocalRing S (closedFiberOpenPoint S y hy)))
    (s d : ℤ)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (h_dualizing : ∃ K : DerivedCategory.{u + 1} (ModuleCat.{u} A),
      K.IsCanonicalDualizingComplex CA) :
    SatisfiesInequalities S F s (s + d) ↔
      HasAlgebraizationSituationAtDistance S F Clocal s d := sorry

/-- Under the cohomological-dimension and dualizing hypotheses, strict `(s, s + d)`
inequalities imply ordinary `(s, s + d)` inequalities. -/
theorem inequalities_of_strict (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    [hmonA : MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u} A))]
    (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A)) (s d : ℤ)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (h_dualizing : ∃ K : DerivedCategory.{u + 1} (ModuleCat.{u} A),
      K.IsCanonicalDualizingComplex CA)
    (hF : SatisfiesStrictInequalities S F s (s + d)) :
    SatisfiesInequalities S F s (s + d) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
