/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section.Affine
import StacksCheckRecall

/-!
# Remark 31.29.5

Support and colimit descriptions for a rank-one reflexive section in the affine setting.

@stack 0EBQ
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 31.29.5 (1): For a nonzero section of a finite rank-one reflexive module over a
Noetherian normal domain, the open where the section trivializes the module is the complement
of the zero loci of the height-one primes in the support of its cokernel. -/
@[stacks 0EBQ] #check
  (AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionIsoLocus_eq_compl_iUnion_zeroLocus :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R],
      ∀ (ℱ : (Spec (CommRingCat.of R)).Modules) [ℱ.IsCoherent]
        [Scheme.Modules.IsRankOneReflexive (Spec (CommRingCat.of R)) ℱ]
        (s : 𝟙_ (Spec (CommRingCat.of R)).Modules ⟶ ℱ),
        s ≠ 0 → ∀ (U : (Spec (CommRingCat.of R)).Opens),
          (U : Set (Spec (CommRingCat.of R))) =
            Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s →
            ∀ {r : ℕ} (p : Fin r → PrimeSpectrum R),
              (∀ i, (p i).asIdeal.height = 1) →
                (∀ i, p i ∈ AlgebraicGeometry.RingedSpace.moduleSupport (cokernel s)) →
                  (∀ q : PrimeSpectrum R,
                    q.asIdeal.height = 1 →
                      q ∈ AlgebraicGeometry.RingedSpace.moduleSupport (cokernel s) →
                        ∃ i : Fin r, q = p i) →
                    (U : Set (Spec (CommRingCat.of R))) =
                      (⋃ i : Fin r,
                        PrimeSpectrum.zeroLocus ((p i).asIdeal : Set R))ᶜ)

/- Remark 31.29.5 (2): In the same setting, the global sections of the structure sheaf on the
trivialization open are the colimit of the reflexive tensor powers of the module. -/
@[stacks 0EBQ] #check
  (AlgebraicGeometry.Scheme.Modules.globalSectionsTensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R],
      ∀ (ℱ : (Spec (CommRingCat.of R)).Modules) [ℱ.IsCoherent]
        [Scheme.Modules.IsRankOneReflexive (Spec (CommRingCat.of R)) ℱ]
        (s : 𝟙_ (Spec (CommRingCat.of R)).Modules ⟶ ℱ),
        s ≠ 0 → ∀ (U : (Spec (CommRingCat.of R)).Opens),
          (U : Set (Spec (CommRingCat.of R))) =
            Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s →
            Nonempty
              (Scheme.Hom.globalSectionsMod U.ι
                  (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules) ≅
                colimit (Scheme.Modules.rankOneReflexiveSectionPowerDiagram s ⋙
                  AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R))))
