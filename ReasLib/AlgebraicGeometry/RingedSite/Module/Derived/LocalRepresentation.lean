/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- The named ringed-site models unfold to this standard quotient; infer it
-- directly when the site is hidden behind a localized/source ModuleCat alias.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
-- Local instance justification (proof-local temporary data): the localized-complex and mapDerivedCategory comparisons below need both exactness proofs for the fixed localizedRestriction functor; install the named finite-limit and finite-colimit proofs only in this module.
attribute [local instance] RingedSite.Hom.localizedRestriction_preservesFiniteLimits
  RingedSite.Hom.localizedRestriction_preservesFiniteColimits

/-!
# Local representatives of derived morphisms on ringed sites

This file owns the cover-wise interface for representing a derived morphism by chain maps and
for null-homotopies after localization.  The API is stated for bundled ringed sites, so consumers
do not have to expose the sheafification, exactness, and derived-category implementation of every
slice presentation.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]

/-- A derived morphism is represented on `U` when its localization is carried by an actual
morphism of localized complexes through the canonical derived comparison isomorphisms. -/
@[stacks 08C9 "chain-map representation after localization"]
def IsRepresentedOn
    (E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : X) : Prop :=
  ∃ β : (localizedRestrictionComplex.{w} X U).obj E ⟶
      (localizedRestrictionComplex.{w} X U).obj F,
    CommSq
      ((localizedRestrictionDerived.{w} X U).map α)
      ((localizedRestriction.{w} X U).mapDerivedCategoryFactors.app E).hom
      ((localizedRestriction.{w} X U).mapDerivedCategoryFactors.app F).hom
      (DerivedCategory.Q.map β)

/-- A derived morphism is locally represented at `U` when it is represented on every member of
some covering of `U`. -/
@[stacks 08C9 "cover-wise chain-map representation"]
def IsLocallyRepresentedAt
    (E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : X) : Prop :=
  ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow, IsRepresentedOn E F α I.Y

/-- A morphism of complexes is null-homotopic on `U` when its localized morphism is homotopic
to zero. -/
@[stacks 08C9 "null-homotopy after localization"]
def IsNullHomotopicOn
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (α : E ⟶ F) (U : X) : Prop :=
  Nonempty (Homotopy ((localizedRestrictionComplex.{w} X U).map α) 0)

/-- A morphism of complexes is locally null-homotopic at `U` when it is null-homotopic on every
member of some covering of `U`. -/
@[stacks 08C9 "cover-wise null-homotopy"]
def IsLocallyNullHomotopicAt
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (α : E ⟶ F) (U : X) : Prop :=
  ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow, IsNullHomotopicOn α I.Y

/-- Unfolding `IsRepresentedOn` gives the canonical comparison square and its chain-map
representative. -/
theorem isRepresentedOn_iff
    (E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : X) :
    IsRepresentedOn E F α U ↔
      ∃ β : (localizedRestrictionComplex.{w} X U).obj E ⟶
          (localizedRestrictionComplex.{w} X U).obj F,
        CommSq
          ((localizedRestrictionDerived.{w} X U).map α)
          ((localizedRestriction.{w} X U).mapDerivedCategoryFactors.app E).hom
          ((localizedRestriction.{w} X U).mapDerivedCategoryFactors.app F).hom
          (DerivedCategory.Q.map β) := sorry

/-- Unfolding `IsLocallyRepresentedAt` gives its cover-wise representation criterion. -/
theorem isLocallyRepresentedAt_iff
    (E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : X) :
    IsLocallyRepresentedAt E F α U ↔
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow, IsRepresentedOn E F α I.Y := sorry

/-- Unfolding `IsNullHomotopicOn` gives the localized null-homotopy criterion. -/
theorem isNullHomotopicOn_iff
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (α : E ⟶ F) (U : X) :
    IsNullHomotopicOn α U ↔
      Nonempty (Homotopy ((localizedRestrictionComplex.{w} X U).map α) 0) := sorry

/-- Unfolding `IsLocallyNullHomotopicAt` gives its cover-wise null-homotopy criterion. -/
theorem isLocallyNullHomotopicAt_iff
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (α : E ⟶ F) (U : X) :
    IsLocallyNullHomotopicAt α U ↔
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow, IsNullHomotopicOn α I.Y := sorry

namespace IsStrictlyPerfect

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A derived morphism out of a strictly perfect complex is locally represented by chain maps at
every object of the ringed site. -/
@[stacks 08C9 "strictly perfect source", stacks 08FR "(1)"]
theorem locallyRepresentedAt
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : X) :
    IsLocallyRepresentedAt E F α U := sorry

/-- A chain map out of a strictly perfect complex which vanishes in the derived category is
locally null-homotopic at every object of the ringed site. -/
@[stacks 08C9 "strictly perfect source", stacks 08FR "(2)"]
theorem locallyNullHomotopicAt
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsStrictlyPerfect E)
    (α : E ⟶ F)
    (hα : DerivedCategory.Q.map α =
      (0 : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)) (U : X) :
    IsLocallyNullHomotopicAt α U := sorry

end IsStrictlyPerfect

end RingedSite.CochainComplex
