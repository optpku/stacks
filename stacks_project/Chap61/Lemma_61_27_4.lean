/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.DerivedComparison
import StacksCheckRecall

/-!
# Lemma 61.27.4

Derived inverse image `ε⁻¹` along `etaleToProEt` is an equivalence between
the bounded-below derived categories of complexes whose cohomology sheaves are
constructible sheaves of `Λ`-modules.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]

/- Lemma 61.27.4: for a scheme `X` and a Noetherian ring `Λ`, writing
`D_c⁺(X.Etale, Λ)` and `D_c⁺(X.ProEt, Λ)` for
`Plus.CohomologyIn (constructibleEtaleModule X Λ)` and
`Plus.CohomologyIn (constructibleProEtaleModule X Λ)`, derived inverse
image `ε⁻¹ = etaleToProEt_modulePlusPullback_constructibleModule` is an
equivalence `D_c⁺(X.Etale, Λ) ≌ D_c⁺(X.ProEt, Λ)`. -/
@[stacks 09AL] #check
  (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullback_constructibleModule_isEquivalence X Λ :
    (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullback_constructibleModule X Λ).IsEquivalence)

end AlgebraicGeometry.Scheme

end

end
