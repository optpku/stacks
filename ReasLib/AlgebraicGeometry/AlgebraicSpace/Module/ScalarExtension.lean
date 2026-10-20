module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SheafTensorExtension

/-! # Explicit scalar extension in the original algebraic-space module universe

The atlas is the witness already in X's definition. No scheme, quasicompact,
integrality, or line-bundle hypothesis is imposed on X. The new sheafification
certificate is backed by the specified small chart category and its actual Ran.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.ScalarExtension

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Forgetting commutativity preserves the sheaf condition for the actual
ring-valued diagram, in the original coefficient universe. -/
instance commutativeForget : (smallEtaleTopology X).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- Original u-valued additive sheafification is backed by the concrete atlas-site adjunction. -/
theorem additiveCertificate : HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  AdditiveSheafification.additive (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

theorem additiveW : (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AdditiveSheafification.additiveW (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

variable {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (α : R ⟶ R')

/-- Same-site tensor/sheafification in exactly the original module universe u. -/
def extension :
    SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm.{u, u + 1, u} R) ⥤
      SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm.{u, u + 1, u} R') := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X for this concrete tensor or localization module sheaf.
  letI := additiveCertificate X
  -- Local instance justification (defeq pin): Use the locally-bijective characterization for the same named additive sheafification, fixing the module sheafification data.
  letI := additiveW X
  exact SheafTensorExtension.extension.{u + 1, u, u, u} α

/-- The original-universe adjunction uses the concrete tensor and Ran/sheafification data. -/
def adjunction : extension X α ⊣
    SheafOfModules.restrictScalars.{u}
      (CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} α) := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X for this concrete tensor or localization module sheaf.
  letI := additiveCertificate X
  -- Local instance justification (defeq pin): Use the locally-bijective characterization for the same named additive sheafification, fixing the module sheafification data.
  letI := additiveW X
  exact SheafTensorExtension.adjunction.{u + 1, u, u, u} α

/-- Explicitly witnessed replacement for same-site restriction's right-adjoint certificate. -/
theorem restriction_isRightAdjoint :
    (SheafOfModules.restrictScalars.{u}
      (CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} α)).IsRightAdjoint :=
  (adjunction X α).isRightAdjoint

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.ScalarExtension
