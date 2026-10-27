/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Definition_52_19_1
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Elementary
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.19.2 (1) -/
@[stacks 0EJ4]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.inequalities_of_isAnnihilatedByIdealPower
  (A := A) :
  (S : AffineAlgebraizationSetup A) →
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) →
    (a b : ℤ) →
    IsAnnihilatedByIdealPowerOnAffineOpens
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) F →
    SatisfiesInequalities S F a b)

/- Lemma 52.19.2 (2) -/
@[stacks 0EJ4]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.strictInequalities_of_inequalities_add_one
  (A := A) :
  (S : AffineAlgebraizationSetup A) →
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) →
    (a b : ℤ) →
    SatisfiesInequalities S F (a + 1) b →
    SatisfiesStrictInequalities S F a b)

/- Lemma 52.19.2 (3) -/
@[stacks 0EJ4]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.inequalities_iff_algebraizationSituation
  (A := A) :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    [hmonA : MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u} A))] →
    (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A)) →
    [hmon : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u}
        (completedLocalRing S (closedFiberOpenPoint S y hy))))] →
    (Clocal : ∀ y : S.Y, ∀ hy : S.y y ∈ S.U,
      CategoryTheory.DerivedCategory.CanonicalClosedPresentation
        (A := completedLocalRing S (closedFiberOpenPoint S y hy))) →
    (s d : ℤ) →
    Ideal.LocalCohomology.HasDimensionLE S.I d →
    (∃ K : DerivedCategory.{u + 1} (ModuleCat.{u} A),
      K.IsCanonicalDualizingComplex CA) →
    (SatisfiesInequalities S F s (s + d) ↔
      HasAlgebraizationSituationAtDistance S F Clocal s d))

/- Lemma 52.19.2 (4) -/
@[stacks 0EJ4]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.inequalities_of_strict (A := A) :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    [hmonA : MonoidalCategory (DerivedCategory.{u + 1} (ModuleCat.{u} A))] →
    (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A)) →
    (s d : ℤ) →
    Ideal.LocalCohomology.HasDimensionLE S.I d →
    (∃ K : DerivedCategory.{u + 1} (ModuleCat.{u} A),
      K.IsCanonicalDualizingComplex CA) →
    SatisfiesStrictInequalities S F s (s + d) →
    SatisfiesInequalities S F s (s + d))

end AlgebraicGeometry.Scheme.CoherentFormalModules
