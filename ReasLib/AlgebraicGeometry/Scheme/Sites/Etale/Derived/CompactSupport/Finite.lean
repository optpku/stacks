/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.CrossRefAttribute

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

variable {k : Type u} [Field k]
variable {Λ : Type u} [CommRing Λ] [h_noeth : IsNoetherianRing Λ]
variable (X : SchemeOverField k)
variable [h_sep : IsSeparated X.hom] [h_ft : Scheme.Hom.FiniteType X.hom]
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

include h_noeth h_sep h_ft

/-- Over an algebraically closed field, compactly supported cohomology of a
bounded-below complex with torsion constructible cohomology on a separated
finite-type scheme is finite over the Noetherian coefficient ring in every
integer degree. -/
@[stacks 0GLH]
theorem etaleDerivedCohomologyCompactSupport_finite_of_plusTorsionConstructible
    [IsAlgClosed k]
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (h_bdd : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (i : ℤ) :
    Module.Finite Λ (etaleDerivedCohomologyCompactSupport P i K) :=
  sorry

/-- Over an algebraically closed field, compactly supported cohomology of a
complex with constructible cohomology on a separated finite-type scheme is finite
in every integer degree when the Noetherian coefficient ring is torsion. -/
@[stacks 0GLH]
theorem etaleDerivedCohomologyCompactSupport_finite_of_isTorsion
    [IsAlgClosed k]
    (hΛ : AddMonoid.IsTorsion Λ)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (i : ℤ) :
    Module.Finite Λ (etaleDerivedCohomologyCompactSupport P i K) :=
  sorry

/-- Compactly supported cohomology of a constructible admissible complex on a
separated finite-type scheme over an algebraically closed field is finite over
the Noetherian coefficient ring in every integer degree. -/
instance instModuleFiniteEtaleDerivedCohomologyCompactSupport [IsAlgClosed k]
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    [h_cons : Fact (
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)]
    [h_adm : Fact (Derived.compactSupportAdmissible X.left Λ K)] (i : ℤ) :
    Module.Finite Λ (etaleDerivedCohomologyCompactSupport P i K) := by
  have h_admissible := h_adm.out
  unfold Derived.compactSupportAdmissible at h_admissible
  rcases h_admissible with ⟨h_tors, h_bdd⟩ | hΛ
  · exact etaleDerivedCohomologyCompactSupport_finite_of_plusTorsionConstructible
      X P K h_cons.out h_tors h_bdd i
  · exact etaleDerivedCohomologyCompactSupport_finite_of_isTorsion
      X P hΛ K h_cons.out i

end AlgebraicGeometry.Scheme.Etale

end
