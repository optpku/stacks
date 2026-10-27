/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section InverseImagePushforward

variable {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u) [Ring Λ]
variable [HasSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : A.Etale,
  HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : B.Etale,
  HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback h).op.HasLeftKanExtension F]
variable [((smallEtalePullback h).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback h).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
variable [IsGrothendieckAbelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The unbounded derived adjunction `g⁻¹ ⊣ Rg_*` on étale sheaves of
`Λ`-modules, obtained by deriving the sheaf-level adjunction
between small-étale inverse image and continuous pushforward and identifying the
K-injective right derived functor with `etaleDerivedPushforward`. -/
def etaleModuleDerivedInverseImageAdjunction :
    etaleModuleDerivedInverseImage h Λ ⊣ etaleDerivedPushforward h :=
  (Adjunction.Derived.KInjective.adjunction
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)))
      ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology)
      ((smallEtalePullback h).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
        B.smallEtaleTopology A.smallEtaleTopology)).ofNatIsoRight
    ((Adjunction.Derived.KInjective.right ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology)).rightDerivedUnique
      (RightDerived.Cochain.functor
        ((smallEtalePullback h).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
      (Adjunction.Derived.KInjective.rightUnit ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
      (RightDerived.Cochain.unit ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)))

/-- The hom-equivalence of the derived inverse-image/pushforward adjunction. -/
def etaleModuleDerivedInverseImageAdjunction_homEquiv
    (K : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)))
    (L : DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))) :
    ((etaleModuleDerivedInverseImage h Λ).obj K ⟶ L) ≃
      (K ⟶ (etaleDerivedPushforward h).obj L) :=
  (etaleModuleDerivedInverseImageAdjunction h Λ).homEquiv K L

/-- The derived inverse-image/pushforward adjunction is the K-injective derived
adjunction of sheaf pullback, transported along uniqueness of right derived
functors onto `etaleDerivedPushforward`. -/
theorem etaleModuleDerivedInverseImageAdjunction_def :
    etaleModuleDerivedInverseImageAdjunction h Λ =
      (Adjunction.Derived.KInjective.adjunction
          (ExactFunctor.of (Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)))
          ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology)
          ((smallEtalePullback h).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            B.smallEtaleTopology A.smallEtaleTopology)).ofNatIsoRight
        ((Adjunction.Derived.KInjective.right
            ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology)).rightDerivedUnique
          (RightDerived.Cochain.functor
        ((smallEtalePullback h).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
          (Adjunction.Derived.KInjective.rightUnit ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
          (RightDerived.Cochain.unit ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
          (HomologicalComplex.quasiIso
            (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))) :=
  sorry

end InverseImagePushforward

end AlgebraicGeometry.Scheme.Etale

end
