/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import stacks_project.Chap71.Definition_71_10_3_MeromorphicSection
import Lean

/-! # Bind proved sheafification certificates to the actual meromorphic owner

All certificates here live in the original coefficient universe. Proof
irrelevance identifies the existing owner types; no comparison is selected
from an admitted isomorphism existence statement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory
open PresheafOfModules SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Sheafification

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

theorem additiveCertificate : HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (CoefficientSheafification.additive (smallEtaleTopology X)).isRightAdjoint

theorem ringCertificate : HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (CoefficientSheafification.commRing (smallEtaleTopology X)).isRightAdjoint

theorem additiveW : (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  CoefficientSheafification.additiveW (smallEtaleTopology X)

theorem ringW : (smallEtaleTopology X).WEqualsLocallyBijective CommRingCat.{u + 1} :=
  CoefficientSheafification.commRingW (smallEtaleTopology X)

/-- The actual ring unit with its proved left-adjoint certificate explicitly selected. -/
abbrev ringUnit :=
  @CategoryTheory.toSheafify _ _ (smallEtaleTopology X) CommRingCat.{u + 1} _
    (ringCertificate X) (regularStructureSections X).localizationPresheaf

/-- Local injectivity of this actual ring unit, derived from the clean certificate. -/
theorem ringUnit_injective : Presheaf.IsLocallyInjective (smallEtaleTopology X) (ringUnit X) := by
  -- Local instance justification (defeq pin): Select the named ring sheafification adjunction at X, matching the already specified ring unit and coefficient sheaf.
  letI := ringCertificate X
  -- Local instance justification (proof-local temporary data): Apply the locally-bijective characterization of that ring sheafification to its actual unit map.
  letI := ringW X
  exact ((smallEtaleTopology X).W_toSheafify
    (regularStructureSections X).localizationPresheaf).isLocallyInjective

theorem ringUnit_surjective : Presheaf.IsLocallySurjective (smallEtaleTopology X) (ringUnit X) := by
  -- Local instance justification (defeq pin): Select the named ring sheafification adjunction at X, matching the already specified ring unit and coefficient sheaf.
  letI := ringCertificate X
  -- Local instance justification (proof-local temporary data): Apply the locally-bijective characterization of that ring sheafification to its actual unit map.
  letI := ringW X
  exact ((smallEtaleTopology X).W_toSheafify
    (regularStructureSections X).localizationPresheaf).isLocallySurjective

theorem ringMap_injective : Presheaf.IsLocallyInjective (smallEtaleTopology X)
    (sheafificationRingMap (smallEtaleTopology X) (regularStructureSections X).localizationPresheaf) := by
  have h := ringUnit_injective X
  exact ⟨h.equalizerSieve_mem⟩

theorem ringMap_surjective : Presheaf.IsLocallySurjective (smallEtaleTopology X)
    (sheafificationRingMap (smallEtaleTopology X) (regularStructureSections X).localizationPresheaf) := by
  have h := ringUnit_surjective X
  exact ⟨h.imageSieve_mem⟩

/-- Reconstruct the existing meromorphic module sheaf with explicit proved certificates. -/
def sheaf (F : X.Modules) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (meromorphicFunctionSheaf X) := by
  -- Local instance justification (defeq pin): Select the named ring sheafification adjunction at X, matching the already specified ring unit and coefficient sheaf.
  letI := ringCertificate X
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X for this concrete tensor or localization module sheaf.
  letI := additiveCertificate X
  -- Local instance justification (defeq pin): Use the locally-bijective characterization for the same named additive sheafification, fixing the module sheafification data.
  letI := additiveW X
  -- Local instance justification (defeq pin): Supply local injectivity of the specified localization-ring sheafification map used for this module extension.
  letI := ringMap_injective X
  -- Local instance justification (defeq pin): Supply local surjectivity of that same localization-ring map used for this module extension.
  letI := ringMap_surjective X
  exact (moduleSheafification (smallEtaleTopology X)
    (regularStructureSections X).localizationPresheaf).obj (meromorphicSectionPresheaf X F)

/-- The reconstructed owner has the same data interface; equality is proof irrelevance. -/
theorem sheaf_eq (F : X.Modules) : sheaf X F = meromorphicSectionSheaf X F := rfl

/-- The actual unit computed using the same proved certificate route. -/
def unit (F : X.Modules) :
    meromorphicSectionPresheaf X F ⟶
      (PresheafOfModules.restrictScalars
        (sheafificationRingMap (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf)).obj
        (meromorphicSectionSheaf X F).val := by
  -- Local instance justification (defeq pin): Select the named ring sheafification adjunction at X, matching the already specified ring unit and coefficient sheaf.
  letI := ringCertificate X
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X for this concrete tensor or localization module sheaf.
  letI := additiveCertificate X
  -- Local instance justification (defeq pin): Use the locally-bijective characterization for the same named additive sheafification, fixing the module sheafification data.
  letI := additiveW X
  -- Local instance justification (defeq pin): Supply local injectivity of the specified localization-ring sheafification map used for this module extension.
  letI := ringMap_injective X
  -- Local instance justification (defeq pin): Supply local surjectivity of that same localization-ring map used for this module extension.
  letI := ringMap_surjective X
  exact (PresheafOfModules.sheafificationAdjunction
    (sheafificationRingMap (smallEtaleTopology X)
      (regularStructureSections X).localizationPresheaf)).unit.app (meromorphicSectionPresheaf X F)


end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Sheafification
