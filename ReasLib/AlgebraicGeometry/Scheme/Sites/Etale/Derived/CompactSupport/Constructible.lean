/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-!
# Constructible cohomology of compact-support pushforwards

If `S` is Noetherian affine of finite dimension and `X.hom : X.left ⟶ S` is
separated, affine, and smooth of relative dimension `1`, then `Rf_!` of a
constant sheaf of a finite module over a Noetherian torsion ring has
constructible cohomology. The same conclusion holds for a finite-type locally
constant sheaf on an open subscheme of the relative affine line over such a base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section ConstantModule

variable {S : Scheme.{u}} (X : Over S)
variable [IsAffine S] [IsNoetherian S]
variable [IsSeparated X.hom] [IsAffineHom X.hom]
variable [SmoothOfRelativeDimension 1 X.hom] [Scheme.Hom.FiniteType X.hom]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {M : Type u} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
variable (P : Compactification.Of S X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) S.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) S.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ S) (G : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

/-- If `S` is a Noetherian affine scheme of finite dimension,
`f = X.hom : X.left ⟶ S` is separated, affine, and smooth of relative
dimension `1`, `Λ` is a Noetherian torsion ring, and `M` is a finite
`Λ`-module, then `Rf_!` of the constant étale sheaf of `M` has constructible
cohomology sheaves. -/
theorem etaleDerivedLowerShriek_constantModule_cohomology_isConstructible
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim S < ⊤) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            S.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
          ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (.of Λ M)))) :=
  sorry

/-- Each homology sheaf of `Rf_!` of the constant étale sheaf of `M` is a
constructible étale sheaf of `Λ`-modules on `S`. -/
theorem etaleDerivedLowerShriek.constantModule_homology_isConstructible
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim S < ⊤) (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          S.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek X P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
            ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
              (.of Λ M))))) :=
  etaleDerivedLowerShriek_constantModule_cohomology_isConstructible X P hΛ hdim n

end ConstantModule

section LocallyConstant

variable {Y : Scheme.{u}} {U : Scheme.{u}}
variable (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion i]
variable [IsAffine Y] [IsNoetherian Y]
variable [IsSeparated (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
variable [Scheme.Hom.FiniteType (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
variable (P : Compactification.Of Y (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
variable [HasSheafify (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etale,
  HasWeakSheafify ((Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology.over V)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G : (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

namespace etaleDerivedLowerShriek.OpenAffineLine

/-- If `Y` is a Noetherian affine scheme of finite dimension,
`Λ` is a Noetherian torsion ring, `i : U ⟶ 𝔸(ULift (Fin 1); Y)` is an open
immersion, and `F` is a finite-type locally constant étale sheaf of `Λ`-modules
on `U`, then `Rf_! F` has constructible cohomology sheaves, where `f` is the
structure morphism `i ≫ 𝔸(ULift (Fin 1); Y) ↘ Y`. -/
theorem cohomology_isConstructible
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim Y < ⊤) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) (Λ := Λ) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) :=
  sorry

/-- Each homology sheaf of `Rf_! F` is a constructible étale sheaf of
`Λ`-modules on `Y`. -/
theorem homology_isConstructible
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim Y < ⊤) (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) (Λ := Λ) P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
                (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  cohomology_isConstructible
    i F P hΛ hdim n

end etaleDerivedLowerShriek.OpenAffineLine

end LocallyConstant

end AlgebraicGeometry.Scheme.Etale

end
