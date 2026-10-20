/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.CompactSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 63.12.4: if `k` is algebraically closed, `X` is a separated finite-type
scheme over `k` of dimension at most one, `Λ` is Noetherian, and `F` is a
constructible torsion sheaf of `Λ`-modules on `X_étale`, then compactly
supported étale cohomology `H^q_c(X, F)` is a finite `Λ`-module. -/
@[stacks 0GKR] #check (AlgebraicGeometry.Scheme.Etale.etaleCohomologyCompactSupport_finite_of_constructible :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    (X : SchemeOverField k)
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : X.left.Etale,
      HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : P.obj.right.left.Etale,
      HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory
      (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u} Λ)]
    [∀ U : (Spec (CommRingCat.of k)).Etale,
      HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
        (ModuleCat.{u} Λ)]
    [HasDerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
        P.obj.right.left.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
          P.obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)]
    [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
        (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
            (ModuleCat.{u} Λ)).obj
          (op (globalEtale (Spec (CommRingCat.of k))))))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ (Y : Scheme.{u}) (f : Y ⟶ X.left) (G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension G]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (h_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            X.left.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (h_torsion :
      Sheaf.IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))
    (q : ℤ),
    Module.Finite Λ
      (etaleDerivedCohomologyCompactSupport P q
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)))

end AlgebraicGeometry.Scheme.Etale

end
