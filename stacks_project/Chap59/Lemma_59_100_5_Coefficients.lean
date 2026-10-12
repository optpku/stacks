/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf/étale comparison coefficients

This leaf owns the abelian inverse image `π_X⁻¹` from the small étale site of a scheme `X` to the
big étale slice, together with the essential-image coefficient family used by the fppf/étale
topology-comparison situation.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

variable (X : Scheme.{u})
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]

/-- Inverse image `π_X⁻¹` on abelian sheaves along identity-base étale relocalization, at the
coefficient universe required by `TopologyComparison.Situation` on `Scheme.{u}`. -/
abbrev piInverseImage :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Direct image `π_{X,*}` on abelian sheaves along identity-base étale relocalization. -/
abbrev piPushforward :
    Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Sheaf-level adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
def piAdjunction : piInverseImage X ⊣ piPushforward X :=
  (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- The source coefficient family `A'_X` consisting of sheaves of the form `π_X⁻¹ F`. -/
@[stacks 0F0H "essential image of the small-to-big étale inverse image"]
abbrev essImageAb :
    ObjectProperty (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  Functor.essImage (piInverseImage X)

/-- Every canonical inverse-image object belongs to `essImageAb X`. -/
theorem obj_mem_essImageAb
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    essImageAb X ((piInverseImage X).obj F) := sorry

/-- Membership in the essential-image coefficient family is detected by the adjunction counit. -/
theorem mem_essImageAb_iff_counit_isIso
    (ℱ : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :
    essImageAb X ℱ ↔ IsIso ((piAdjunction X).counit.app ℱ) := sorry

/-- The essential-image coefficient family is a weak Serre class. -/
@[stacks 0F0H "weak Serre essential image"]
instance essImageAb_isWeakSerre
    [Abelian (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})] :
    IsWeakSerreClass (essImageAb X) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end
