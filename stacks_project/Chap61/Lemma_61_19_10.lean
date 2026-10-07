module

public import stacks_project.Chap61.Lemma_61_19_10_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.10

Derived inverse image `ε⁻¹` along `etaleToProEt` is an equivalence between
the bounded-below derived categories of complexes whose cohomology sheaves are
locally constant of finite type.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.ProEt,
    HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)]

/-- Lemma 61.19.10: for a scheme `X` and a Noetherian ring `Λ`, derived inverse
image `ε⁻¹ = etaleToProEt_modulePlusPullback` restricts to an equivalence
`Plus.CohomologyIn (finiteTypeLocallyConstantModule X.smallEtaleTopology Λ) ≌
Plus.CohomologyIn (finiteTypeLocallyConstantModule (ProEt.topology X) Λ)`
between the full subcategories of `D⁺(X.Etale, Λ)` and `D⁺(X.ProEt, Λ)`
consisting of complexes whose cohomology sheaves are locally constant sheaves
of finite-type `Λ`-modules. -/
@[stacks 099Z]
instance etaleToProEt_modulePlusPullback_locallyConstantFiniteType_isEquivalence :
    (etaleToProEt_modulePlusPullback_locallyConstantFiniteType X Λ).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme

end

end
