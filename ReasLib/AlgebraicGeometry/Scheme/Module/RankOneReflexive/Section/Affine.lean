/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section.Codimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine descriptions attached to rank-one reflexive sections

This file owns the support description of the isomorphism locus and the section-power colimit
comparison used in the affine normal-domain setting.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- For a nonzero section of a coherent rank-one reflexive module on the spectrum of a
Noetherian normal domain, its isomorphism locus is the complement of the union of the zero loci
of the height-one primes in the support of its cokernel. -/
@[stacks 0EBQ]
theorem rankOneReflexiveSectionIsoLocus_eq_compl_iUnion_zeroLocus
    (ℱ : (Spec (CommRingCat.of R)).Modules) [ℱ.IsCoherent]
    [IsRankOneReflexive (Spec (CommRingCat.of R)) ℱ]
    (s : 𝟙_ (Spec (CommRingCat.of R)).Modules ⟶ ℱ) (hs : s ≠ 0)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of R))) = rankOneReflexiveSectionIsoLocusSet s)
    {r : ℕ} (p : Fin r → PrimeSpectrum R)
    (hp_height : ∀ i, (p i).asIdeal.height = 1)
    (hp_support : ∀ i, p i ∈ RingedSpace.moduleSupport (cokernel s))
    (hp_complete : ∀ q : PrimeSpectrum R,
      q.asIdeal.height = 1 → q ∈ RingedSpace.moduleSupport (cokernel s) →
        ∃ i : Fin r, q = p i) :
    (U : Set (Spec (CommRingCat.of R))) =
      (⋃ i : Fin r, PrimeSpectrum.zeroLocus ((p i).asIdeal : Set R))ᶜ := sorry

/-- Global sections of the structure module on the isomorphism locus of a nonzero section of a
coherent rank-one reflexive module over an affine normal domain form the colimit of its
reflexive section-power diagram. -/
@[stacks 0EBQ]
theorem globalSectionsTensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram
    (ℱ : (Spec (CommRingCat.of R)).Modules) [ℱ.IsCoherent]
    [IsRankOneReflexive (Spec (CommRingCat.of R)) ℱ]
    (s : 𝟙_ (Spec (CommRingCat.of R)).Modules ⟶ ℱ) (hs : s ≠ 0)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of R))) = rankOneReflexiveSectionIsoLocusSet s) :
    Nonempty
      (Scheme.Hom.globalSectionsMod U.ι
          (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules) ≅
        colimit (rankOneReflexiveSectionPowerDiagram s ⋙
          moduleSpecΓFunctor (R := CommRingCat.of R))) := sorry

end AlgebraicGeometry.Scheme.Modules
