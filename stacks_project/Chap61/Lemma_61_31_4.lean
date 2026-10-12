/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_31_3
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.31.4

Restriction of abelian sheaves along the inclusion of a contained big pro-étale
site of `S` does not change objectwise cohomology, and every abelian sheaf on
the smaller site extends to a larger contained big pro-étale site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry

noncomputable section

universe u v v' w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {Y : ChosenBigProetaleSite.{u, v'}}
variable (incl : X.carrier ⥤ Y.carrier)

/-- Lemma 61.31.4 (1): for an abelian sheaf on a larger contained big pro-étale
site of `S`, degree-`p` cohomology over an object `U` of the smaller site agrees
with cohomology of the restriction of that sheaf to the smaller site. -/
@[stacks 0F4T]
def containedSliceInclusion_cohomology_restrict
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [HasSheafify (X.bigTopology S) AddCommGrpCat.{w}]
    [HasSheafify (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (X.bigTopology S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian
      (Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
        AddCommGrpCat.{w})]
    [HasInjectiveResolutions
      (Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
        AddCommGrpCat.{w})]
    (p : ℕ) (U : X.bigSite S)
    (F' : Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      AddCommGrpCat.{w}) :
    (((Over.post (containedInclusion incl e hcov)).sheafPushforwardContinuous
          AddCommGrpCat.{w} (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S)) ⋙
        siteAbelianSectionsFunctor (X.bigTopology S) U).rightDerived p).obj F' ≅
      ((siteAbelianSectionsFunctor
          (Y.bigTopology ((containedInclusion incl e hcov).obj S))
          ((Over.post (containedInclusion incl e hcov)).obj U)).rightDerived p).obj F' :=
  (SiteAbelianSectionsDerived.derivedSectionsIso
      (Over.post (containedInclusion incl e hcov)) p U).app F'

/-- The contained slice-inclusion restriction comparison is the Sites 21.7.2
derived sections isomorphism at `F'`. -/
theorem containedSliceInclusion_cohomology_restrict_eq
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [HasSheafify (X.bigTopology S) AddCommGrpCat.{w}]
    [HasSheafify (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (X.bigTopology S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian
      (Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
        AddCommGrpCat.{w})]
    [HasInjectiveResolutions
      (Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
        AddCommGrpCat.{w})]
    (p : ℕ) (U : X.bigSite S)
    (F' : Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      AddCommGrpCat.{w}) :
    containedSliceInclusion_cohomology_restrict incl e hcov S p U F' =
      (SiteAbelianSectionsDerived.derivedSectionsIso
          (Over.post (containedInclusion incl e hcov)) p U).app F' := sorry

/-- The canonical extension of an abelian sheaf along a contained big pro-étale
slice inclusion, given by cocontinuous sheaf pushforward. -/
def containedSliceInclusion_extension
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [∀ P : (X.bigSite S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P]
    (F : Sheaf (X.bigTopology S) AddCommGrpCat.{w}) :
    Sheaf (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      AddCommGrpCat.{w} :=
  ((Over.post (containedInclusion incl e hcov)).sheafPushforwardCocontinuous
      AddCommGrpCat.{w} (X.bigTopology S)
      (Y.bigTopology ((containedInclusion incl e hcov).obj S))).obj F

/-- The contained slice-inclusion extension is cocontinuous sheaf pushforward. -/
theorem containedSliceInclusion_extension_eq
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [∀ P : (X.bigSite S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P]
    (F : Sheaf (X.bigTopology S) AddCommGrpCat.{w}) :
    containedSliceInclusion_extension incl e hcov S F =
      ((Over.post (containedInclusion incl e hcov)).sheafPushforwardCocontinuous
          AddCommGrpCat.{w} (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S))).obj F := sorry

/-- Lemma 61.31.4 (2): every abelian sheaf on a contained big pro-étale site of
`S` is isomorphic to the restriction of its canonical extension to a larger
contained big pro-étale site. -/
@[stacks 0F4T]
def containedSliceInclusion_extension_restrict
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [∀ P : (X.bigSite S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P]
    (F : Sheaf (X.bigTopology S) AddCommGrpCat.{w}) :
    ((Over.post (containedInclusion incl e hcov)).sheafPushforwardContinuous
          AddCommGrpCat.{w} (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S))).obj
      (containedSliceInclusion_extension incl e hcov S F) ≅ F :=
  @asIso _ _ _ _
    (((Over.post (containedInclusion incl e hcov)).sheafAdjunctionCocontinuous
        AddCommGrpCat.{w} (X.bigTopology S)
        (Y.bigTopology ((containedInclusion incl e hcov).obj S))).counit.app F)
    (sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
      (X.bigTopology S)
      (Y.bigTopology ((containedInclusion incl e hcov).obj S))
      (Over.post (containedInclusion incl e hcov)) F)

/-- The contained slice-inclusion extension comparison is the Sites 7.21.8
counit isomorphism at `F`. -/
theorem containedSliceInclusion_extension_restrict_eq
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [∀ P : (X.bigSite S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P]
    (F : Sheaf (X.bigTopology S) AddCommGrpCat.{w}) :
    containedSliceInclusion_extension_restrict incl e hcov S F =
      @asIso _ _ _ _
        (((Over.post (containedInclusion incl e hcov)).sheafAdjunctionCocontinuous
            AddCommGrpCat.{w} (X.bigTopology S)
            (Y.bigTopology ((containedInclusion incl e hcov).obj S))).counit.app
          F)
        (sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
          (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S))
          (Over.post (containedInclusion incl e hcov)) F) := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
