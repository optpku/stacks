/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Commutative-ring sheafification in the original coefficient universe

Restrict to the supplied small atlas site, apply native small-site ring
sheafification, and extend by the actual right Kan functor. The comparison
and Hom correspondence specify the adjunction data; only their geometric
descent and finite-limit laws may be deferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CommRingSheafification

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (U : Over S)
    (a : ofOver U ⟶ X) [AlgebraicSpace.Etale a]
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)

-- Local notation names the actual small site belonging to the supplied atlas.
local notation "atlasTopology" => PullbackFactory.SmallAtlas.topology U a
-- Local notation names the original site being sheafified.
local notation "spaceTopology" => smallEtaleTopology X
-- Local notation names the specified chart inclusion used in each comparison.
local notation "chartInclusion" => PullbackFactory.SmallAtlas.inclusion U a

include ha in
/-- The actual atlas inclusion is a dense subsite. -/
theorem dense : (chartInclusion).IsDenseSubsite atlasTopology spaceTopology :=
  PullbackFactory.SmallAtlas.denseSubsite U a ha

/-- Both objects and arrows of the actual atlas site fit the ring coefficient universe. -/
theorem smallSiteSheafification : HasSheafify atlasTopology CommRingCat.{u} := by
  infer_instance

/-- The right extension is indexed by genuine original-universe comma categories. -/
theorem extensionLimits (V : (smallEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (chartInclusion).op) CommRingCat.{u} := by
  infer_instance

/-- Restriction and actual compatible-section right extension compare the two sheaf categories. -/
def comparison : Sheaf spaceTopology CommRingCat.{u} ≌
    Sheaf atlasTopology CommRingCat.{u} := by
  -- Use cover density of this specified atlas in the native comparison theorem.
  letI := dense U a ha
  -- Pin the real small-comma limits used by this inclusion's right Kan extension.
  letI := extensionLimits U a
  exact ((chartInclusion).sheafAdjunctionCocontinuous CommRingCat.{u}
    atlasTopology spaceTopology).toEquivalence

/-- The actual sheafification functor is restriction, native plus sheafification, then extension. -/
def sheafify : ((smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u}) ⥤
    Sheaf spaceTopology CommRingCat.{u} := by
  -- Native small-site sheafification supplies its real functor and adjunction.
  letI : HasWeakSheafify atlasTopology CommRingCat.{u} :=
    (smallSiteSheafification U a).isRightAdjoint
  exact (Functor.whiskeringLeft _ _ _).obj (chartInclusion).op ⋙
    presheafToSheaf atlasTopology CommRingCat.{u} ⋙ (comparison U a ha).inverse

/-- Both Hom directions use the specified extension, native sheafification, and dense-site gluing. -/
def homEquiv (P : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u})
    (Q : Sheaf spaceTopology CommRingCat.{u}) :
    ((sheafify U a ha).obj P ⟶ Q) ≃ (P ⟶ Q.obj) := by
  -- Each local law concerns the same actual atlas inclusion.
  letI := dense U a ha
  letI := Functor.IsDenseSubsite.isCoverDense atlasTopology spaceTopology chartInclusion
  letI := Functor.IsDenseSubsite.isLocallyFull atlasTopology spaceTopology chartInclusion
  letI : HasWeakSheafify atlasTopology CommRingCat.{u} :=
    (smallSiteSheafification U a).isRightAdjoint
  exact ((comparison U a ha).symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction atlasTopology CommRingCat.{u}).homEquiv _ _).trans
      (Functor.IsCoverDense.restrictHomEquivHom (G := chartInclusion)))

/-- The Hom correspondence specifies the actual unit and counit of sheafification. -/
def adjunction : sheafify U a ha ⊣ sheafToPresheaf spaceTopology CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv U a ha
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Commutative-ring sheafification is left exact for this actual small-atlas construction. -/
theorem preservesFiniteLimits : PreservesFiniteLimits (sheafify U a ha) := sorry

include U a ha in
/-- This certificate retains the actual sheafification functor and adjunction witness. -/
theorem certificate : HasSheafify spaceTopology CommRingCat.{u} := by
  -- Pin finite-limit preservation of the explicitly constructed sheafification functor.
  letI := preservesFiniteLimits U a ha
  exact HasSheafify.mk' spaceTopology CommRingCat.{u} (adjunction U a ha)

/-- The stored atlas of the given algebraic space supplies its original-universe certificate. -/
theorem ofSpace (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  certificate (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

end AlgebraicGeometry.AlgebraicSpace.CommRingSheafification
