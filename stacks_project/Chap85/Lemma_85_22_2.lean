/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedModuleDescent
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.DerivedAdjunction

/-!
# Lemma 85.22.2

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `U` be a hypercovering of `X` in `C`. For every `E` in
`D(O_X)`, the canonical derived-unit map `E ⟶ Ra_* La^* E` is an isomorphism.
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

/- Lemma 85.22.2: Let `C` be a site with fibre products and `X` an object of
`C`. Let `O_C` be a sheaf of rings. Let `U` be a hypercovering of `X` in `C`.
For `E ∈ D(O_X)` the map `E ⟶ Ra_* La^* E` is an isomorphism. -/
@[stacks 0DAC] #check
  (RingedSite.Localization.AtSimplicialSR.derivedUnit_app_isIso
    (X := X.localization A.right)
    (K := toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)) :
    ∀ E : Hom.ModuleDerived.{w} (X.localization A.right),
      IsIso ((RingedSite.Hypercovering.derivedUnit A.right (toHypercovering.{ι} A hA)).app E))

/- The derived unit `𝟭 ⟶ La^* ⋙ Ra_*` is an isomorphism of functors on `D(O_X)`. -/
#check
  (RingedSite.Localization.AtSimplicialSR.derivedUnit_isIso
    (X := X.localization A.right)
    (K := toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)) :
    IsIso (RingedSite.Hypercovering.derivedUnit A.right (toHypercovering.{ι} A hA)))

end CategoryTheory.SimplicialObject.Augmented
