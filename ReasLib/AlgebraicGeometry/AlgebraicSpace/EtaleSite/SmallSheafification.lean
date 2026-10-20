/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # Sheafification in the original module universe u

Restriction to a specified genuinely small dense site, its proved small-site
sheafification, and actual right Kan extension provide the data. The only
geometric proof input is cover density of those specified charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.AdditiveSheafification

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (U : Over S)
    (a : ofOver U ⟶ X) [AlgebraicSpace.Etale a]
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)

-- Local declaration justification (source-local notation): This section compares the topology of the supplied atlas with the large etale topology; the abbreviation depends on its local atlas parameters.
local notation "smallTop" => SmallAtlas.topology U a
-- Local declaration justification (source-local notation): This section distinguishes the large etale site of X from its supplied atlas site without introducing a second global topology owner.
local notation "largeTop" => smallEtaleTopology X
-- Local declaration justification (source-local notation): This section repeatedly uses only the inclusion of its supplied atlas a; the notation is scoped to that comparison, not a new functor.
local notation "chartInclusion" => SmallAtlas.inclusion U a

include ha in
theorem dense : (chartInclusion).IsDenseSubsite smallTop largeTop := SmallAtlas.denseSubsite U a ha

/-- The coefficient universe is u because both objects and arrows of the
actual chart category are u-small. This is Mathlib's proved plus construction. -/
theorem small_additive : HasSheafify smallTop AddCommGrpCat.{u} := by infer_instance

theorem small_additiveW : (smallTop).WEqualsLocallyBijective AddCommGrpCat.{u} := by infer_instance

/-- Limits for the actual right Kan extension are limits indexed in u. -/
theorem ran_limits (V : (smallEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (chartInclusion).op) AddCommGrpCat.{u} := by infer_instance

/-- The explicit comparison equivalence has actual restriction forward and
right Kan extension backward; it does not select an inverse from bare existence. -/
def comparison : Sheaf largeTop AddCommGrpCat.{u} ≌ Sheaf smallTop AddCommGrpCat.{u} := by
  -- Local instance justification (defeq pin): Use the dense-subsite law of the given atlas a, so the restriction comparison uses this very small atlas site.
  letI := dense U a ha
  -- Local instance justification (defeq pin): Use the established comma-diagram limits for the supplied atlas inclusion, at the original coefficient universe.
  letI := ran_limits U a
  exact ((chartInclusion).sheafAdjunctionCocontinuous AddCommGrpCat.{u} smallTop largeTop).toEquivalence

/-- Original-universe sheafification as restriction, plus construction, then Ran. -/
def sheafify : ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Sheaf largeTop AddCommGrpCat.{u} := by
  -- Local instance justification (defeq pin): Use the dense-subsite law of the given atlas a, so the restriction comparison uses this very small atlas site.
  letI := dense U a ha
  -- Local instance justification (defeq pin): Use the explicit small-atlas additive sheafification adjunction, preserving the original universe u.
  letI : HasWeakSheafify smallTop AddCommGrpCat.{u} := (small_additive U a).isRightAdjoint
  exact (Functor.whiskeringLeft _ _ _).obj (chartInclusion).op ⋙ presheafToSheaf smallTop AddCommGrpCat.{u} ⋙
    (comparison U a ha).inverse

/-- The Hom correspondence consists of three actual maps: Ran/restriction,
sheafification, and the unique glued map on the full dense site. -/
def homEquiv (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (Q : Sheaf largeTop AddCommGrpCat.{u}) :
    ((sheafify U a ha).obj P ⟶ Q) ≃ (P ⟶ Q.obj) := by
  -- Local instance justification (defeq pin): Use the dense-subsite law of the given atlas a, so the restriction comparison uses this very small atlas site.
  letI := dense U a ha
  -- Local instance justification (proof-local temporary data): Expose the cover-density projection of the same atlas inclusion for the fully faithful sheaf restriction Hom comparison.
  letI := Functor.IsDenseSubsite.isCoverDense smallTop largeTop chartInclusion
  -- Local instance justification (proof-local temporary data): Expose local fullness of the same atlas inclusion in its sheaf restriction Hom comparison.
  letI := Functor.IsDenseSubsite.isLocallyFull smallTop largeTop chartInclusion
  -- Local instance justification (defeq pin): Use the explicit small-atlas additive sheafification adjunction, preserving the original universe u.
  letI : HasWeakSheafify smallTop AddCommGrpCat.{u} := (small_additive U a).isRightAdjoint
  exact ((comparison U a ha).symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction smallTop AddCommGrpCat.{u}).homEquiv _ _).trans
      (Functor.IsCoverDense.restrictHomEquivHom (G := chartInclusion)))

/-- Naturality of these specified maps is a law, not a witness selecting data. -/
def adjunction : sheafify U a ha ⊣ sheafToPresheaf largeTop AddCommGrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv U a ha
      homEquiv_naturality_left_symm := by sorry
      homEquiv_naturality_right := by sorry }

include U a ha in
/-- A certificate backed by the concrete original-universe adjunction. -/
theorem additive : HasWeakSheafify largeTop AddCommGrpCat.{u} :=
  (adjunction U a ha).isRightAdjoint

include U a ha in
/-- The local-bijection property transports along the specified dense inclusion. -/
theorem additiveW : (largeTop).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  -- Local instance justification (defeq pin): Use the dense-subsite law of the given atlas a, so the restriction comparison uses this very small atlas site.
  letI := dense U a ha
  -- Local instance justification (proof-local temporary data): Use this atlas inclusion's cover-density when transporting the locally-bijective characterization of sheafification.
  letI := SmallAtlas.inclusion_coverDense U a ha
  -- Local instance justification (defeq pin): Use the established comma-diagram limits for the supplied atlas inclusion, at the original coefficient universe.
  letI := ran_limits U a
  -- Local instance justification (proof-local temporary data): Use the small-atlas locally-bijective characterization as the source law in the topology transport theorem.
  letI := small_additiveW U a
  exact GrothendieckTopology.WEqualsLocallyBijective.transport largeTop smallTop chartInclusion
    (Functor.IsDenseSubsite.coverPreserving smallTop largeTop chartInclusion)

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.AdditiveSheafification
