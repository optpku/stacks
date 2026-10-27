/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.DerivedGlobalSections

/-!
# Lemma 85.22.3

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `U` be a hypercovering of `X` in `C`. Then there is a
canonical isomorphism `RΓ(X, E) ≅ RΓ((C / U)_total, La^* E)` in `D(Ab)` for
every ambient `E` in `D(O_C)`, using its canonical derived restriction to
`D(O_X)` before applying the augmentation pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace CategoryTheory.SimplicialObject.Augmented

variable {X : RingedSite.{u, v, w}}
variable [h_pb : HasPullbacks X.carrier]
include h_pb
variable (A : SimplicialObject.Augmented X.carrier)
variable (hA : A.IsHypercovering X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization A.right).siteTopology
      (toHypercovering.{ι} A hA).toSimplicialObject) (Type w)]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{ι} A hA).toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget (toHypercovering.{ι} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization A.right).siteTopology
    (toHypercovering.{ι} A hA).toSimplicialObject).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [(X.localization A.right).siteTopology.HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [HasWeakSheafify (X.localization A.right).siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify
    (RingedSite.Localization.AtSimplicialSR.site (X := X.localization A.right)
      (toHypercovering.{ι} A hA).toSimplicialObject).siteTopology
    AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (X.localization A.right).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor
    (RingedSite.Localization.AtSimplicialSR.site (X := X.localization A.right)
      (toHypercovering.{ι} A hA).toSimplicialObject).siteTopology
    AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (X.localization A.right))]
variable [IsGrothendieckAbelian
    (RingedSite.ModuleCat.{w}
      (RingedSite.Localization.AtSimplicialSR.site (X := X.localization A.right)
        (toHypercovering.{ι} A hA).toSimplicialObject))]

/- Lemma 85.22.3: Let `C` be a site with fibre products and `X` an object of
`C`. Let `O_C` be a sheaf of rings. Let `U` be a hypercovering of `X` in `C`.
For every ambient `E ∈ D(O_C)`, the canonical comparison evaluated at its
derived restriction to `D(O_X)` is an isomorphism. -/
@[stacks 0DAD] #check
  (RingedSite.Hypercovering.rGammaPullbackComparison_restrict_app_isIso
      A.right (toHypercovering.{ι} A hA) :
    ∀ E : RingedSite.Hom.ModuleDerived.{w} X,
      IsIso ((RingedSite.Hypercovering.rGammaPullbackComparison
        A.right (toHypercovering.{ι} A hA)).app
          ((RingedSite.Hom.localizedRestrictionDerived.{w} X A.right).obj E)))

/- The comparison is also an isomorphism of functors on the localized
derived category `D(O_X)`. -/
#check
  (RingedSite.Localization.AtSimplicialSR.rGammaPullbackComparison_isIso
      (X := X.localization A.right)
      (CategoryTheory.Hypercovering.toSliceTerminal X.siteTopology A.right
        (toHypercovering.{ι} A hA)) :
    IsIso (RingedSite.Hypercovering.rGammaPullbackComparison
      A.right (toHypercovering.{ι} A hA)))

end CategoryTheory.SimplicialObject.Augmented
