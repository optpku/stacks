/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison
import StacksCheckRecall

/-!
# Lemma 61.27.2

Inverse image `ε⁻¹` along `etaleToProEt` is an equivalence between
constructible sheaves of `Λ`-modules on the small étale and small pro-étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type w) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ, (etaleToProEt X).op.HasLeftKanExtension F]

/- Lemma 61.27.2: for a scheme `X` and a Noetherian ring `Λ`, inverse image `ε⁻¹`
along `etaleToProEt` is an equivalence between constructible sheaves of `Λ`-modules
on `X.Etale` and constructible sheaves of `Λ`-modules on `X.ProEt`. -/
@[stacks 09AK] #check
  (AlgebraicGeometry.Scheme.etaleToProEtPullback_constructibleModule_isEquivalence X Λ :
    (AlgebraicGeometry.Scheme.etaleToProEtPullback_constructibleModule X Λ).IsEquivalence)

end AlgebraicGeometry.Scheme
