/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf
open localCohomology
open scoped ModuleCat

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

#check (principalIdeal_le :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (𝔞 : Ideal A) {f : A},
    f ∈ 𝔞 → Ideal.span {f} ≤ 𝔞)
#check (ofPrincipal :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (𝔞 : Ideal A) (f : A),
    f ∈ 𝔞 → AffineAlgebraizationSetup A)
#check (ofPrincipal_spec :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (𝔞 : Ideal A) (f : A),
    ∀ (hf : f ∈ 𝔞),
      (ofPrincipal 𝔞 f hf).I = Ideal.span {f} ∧ (ofPrincipal 𝔞 f hf).a = 𝔞)
#check (idealOnOpen :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A), S.U.toScheme.IdealSheafData)
#check (idealOnOpen_def :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A),
    idealOnOpen S = (Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)
#check (OpenNeighborhoods :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A), Type u)
#check (OpenNeighborhoods.contains :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) (V : OpenNeighborhoods S),
    ((idealOnOpen S).support : Set S.U) ⊆ V)
#check (neighborhoodSectionsDiagram :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules),
    (OpenNeighborhoods S)ᵒᵖ ⥤ Type u)
#check (neighborhoodSectionsDiagram_obj :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules)
    (V : (OpenNeighborhoods S)ᵒᵖ),
    (neighborhoodSectionsDiagram S M).obj V = M.val.obj (op V.unop.val))
#check (neighborhoodQuotientSectionsDiagram :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ),
    (OpenNeighborhoods S)ᵒᵖ ⥤ Type u)
#check (neighborhoodQuotientSectionsDiagram_obj :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ)
    (V : (OpenNeighborhoods S)ᵒᵖ),
    (neighborhoodQuotientSectionsDiagram S M n).obj V =
      (PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n).val.obj (op V.unop.val))
#check neighborhoodQuotientProjection_naturality
#check neighborhoodQuotientProjection
#check neighborhoodQuotientProjection_app
#check neighborhoodQuotientTransition_naturality
#check neighborhoodQuotientTransition
#check neighborhoodQuotientTransition_app
#check neighborhoodQuotientColimitStep
#check neighborhoodQuotientColimitStep_def
#check positiveNeighborhoodSectionsSystem
#check positiveNeighborhoodSectionsSystem_obj
#check neighborhoodSectionsProjection
#check neighborhoodSectionsProjection_naturality
#check neighborhoodSectionsCone
#check neighborhoodSectionsCone_π
#check neighborhoodComparison
#check neighborhoodComparison_fac
#check positiveNeighborhoodSectionsSystem_isomorphic_positiveSectionsSystem
#check (neighborhoodComparison_bijective_of_principal :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞) (M : ModuleCat A)
    [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A]
    (h_regular : IsSMulRegular M f)
    [Module.Finite A
      ((localCohomology 𝔞 1).obj
        (ModuleCat.of A
          (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))))] ,
    Function.Bijective
      (neighborhoodComparison
        (ofPrincipal 𝔞 f hf)
        ((AlgebraicGeometry.tilde M).restrict
          (ofPrincipal 𝔞 f hf).U.ι)))

end AlgebraicGeometry.AffineAlgebraizationSetup
