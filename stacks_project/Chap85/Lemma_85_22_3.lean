/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap85.Lemma_85_20_3

/-!
# Lemma 85.22.3

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `U` be a hypercovering of `X` in `C`. Then there is a
canonical isomorphism `RΓ(X, E) ≅ RΓ((C / U)_total, La^* E)` in `D(Ab)` for
every `E` in `D(O_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open CategoryTheory.Hypercovering (toSliceTerminal)
open RingedSite.Hypercovering
  (rGammaPullbackComparison toAmbient_terminal site_terminal HasModuleDerivedAdjunction)
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
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived
    (toAmbient_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)))]
variable [ToposHom.HasModulePushforwardDerived
    (toAmbient_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)))]
variable [HasModuleDerivedAdjunction A.right (toHypercovering.{ι} A hA)]
variable [HasWeakSheafify (X.localization A.right).siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify
    (site_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))).siteTopology
    AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (X.localization A.right).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor
    (site_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))).siteTopology
    AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (X.localization A.right))]
variable [IsGrothendieckAbelian
    (RingedSite.ModuleCat.{w}
      (site_terminal (X.localization A.right)
        (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))))]

/-- Lemma 85.22.3: Let `C` be a site with fibre products and `X` an object of
`C`. Let `O_C` be a sheaf of rings. Let `U` be a hypercovering of `X` in `C`.
For `E ∈ D(O_X)` the canonical map `RΓ(X, E) ⟶ RΓ((C / U)_total, La^* E)` is an
isomorphism. -/
@[stacks 0DAD]
theorem rGammaPullbackComparison_app_isIso
    (E : Hom.ModuleDerived.{w} (X.localization A.right)) :
    IsIso ((rGammaPullbackComparison A.right (toHypercovering.{ι} A hA)).app E) :=
  sorry

/-- The comparison `RΓ(X, -) ⟶ La^* ⋙ RΓ((C / U)_total, -)` is an isomorphism of
functors on `D(O_X)`. -/
theorem rGammaPullbackComparison_isIso :
    IsIso (rGammaPullbackComparison A.right (toHypercovering.{ι} A hA)) :=
  sorry

end CategoryTheory.SimplicialObject.Augmented
