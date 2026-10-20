/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X' : Over Y) (X : Over Y)
variable (i : X.left ⟶ X'.left) {Λ : Type u} [CommRing Λ]
variable (P' : Compactification.Of Y X')
variable (P : Compactification.Of Y X)
variable [HasSheafify X'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X'.left.Etale,
  HasWeakSheafify (X'.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P'.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P'.obj.right.left.Etale,
  HasWeakSheafify (P'.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P'.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P')).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P')
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P') (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P') (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P'.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P'.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P'.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P'.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P'.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
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
variable [((smallEtalePullback i).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) X'.left.smallEtaleTopology
    X.left.smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback i).sheafPullback
    (ModuleCat.{u} Λ) X'.left.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPullback
    (ModuleCat.{u} Λ) X'.left.smallEtaleTopology X.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPullback
    (ModuleCat.{u} Λ) X'.left.smallEtaleTopology X.left.smallEtaleTopology)]
variable [X'.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Derived lower shriek of the inverse image along a thickening over a base is
isomorphic to the original derived lower shriek on bounded-below objects with
torsion cohomology, for separated finite-type morphisms between quasi-compact
quasi-separated schemes. -/
theorem etaleDerivedLowerShriek_inverseImage_thickening
    [IsThickening i] [IsSeparated X'.hom] [Scheme.Hom.FiniteType X'.hom]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
    (h_comp : i ≫ X'.hom = X.hom)
    (K' : DerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K')
    (n : ℤ) [DerivedCategory.IsGE K' n] :
    IsIsomorphic
      ((etaleDerivedLowerShriek X P).obj
        (((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
            X'.left.smallEtaleTopology X.left.smallEtaleTopology).mapDerivedCategory.obj
          K'))
      ((etaleDerivedLowerShriek X' P').obj K') :=
  sorry

/-- Over a torsion coefficient ring, inverse image along a thickening followed
by derived lower shriek is isomorphic to the original derived lower shriek as
functors on the entire derived category, for separated finite-type morphisms
between quasi-compact quasi-separated schemes. -/
theorem etaleDerivedLowerShriek_inverseImage_thickening_of_isTorsion
    [IsThickening i] [IsSeparated X'.hom] [Scheme.Hom.FiniteType X'.hom]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
    (h_comp : i ≫ X'.hom = X.hom) (hΛ : AddMonoid.IsTorsion Λ) :
    IsIsomorphic
      (((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
          X'.left.smallEtaleTopology X.left.smallEtaleTopology).mapDerivedCategory ⋙
        etaleDerivedLowerShriek X P)
      (etaleDerivedLowerShriek X' P') :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
