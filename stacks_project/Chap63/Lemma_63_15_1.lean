/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.Finite
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

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (X : SchemeOverField k)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X.left) (G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension G]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/- Lemma 63.15.1 (1): compactly supported cohomology of a bounded-below torsion
constructible complex is finite in every integer degree -/
@[stacks 0GLH] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedCohomologyCompactSupport_finite_of_plusTorsionConstructible X P :
    ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (h_bdd : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (i : ℤ),
    Module.Finite Λ (etaleDerivedCohomologyCompactSupport P i K))

/- Lemma 63.15.1 (2): over a torsion coefficient ring, compactly supported
cohomology of any constructible complex is finite in every integer degree -/
@[stacks 0GLH] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedCohomologyCompactSupport_finite_of_isTorsion X P :
    ∀ (hΛ : AddMonoid.IsTorsion Λ)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (i : ℤ),
    Module.Finite Λ (etaleDerivedCohomologyCompactSupport P i K))

end AlgebraicGeometry.Scheme.Etale

end
