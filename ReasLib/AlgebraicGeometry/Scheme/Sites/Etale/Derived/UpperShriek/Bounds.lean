/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Bounds
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
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
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [((etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).IsLeftAdjoint]

namespace etaleDerivedUpperShriek

/-- A torsion coefficient ring gives a uniform lower t-structure displacement for
étale derived upper shriek associated to a finite-type separated morphism. -/
theorem exists_mapsGE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℕ, Functor.TStructure.MapsGE (etaleDerivedUpperShriek X Λ P) t t
      (-(N : ℤ)) :=
  sorry

/-- A uniform lower t-structure displacement for étale derived upper shriek,
expressed on each derived object and integer degree. -/
theorem exists_isGE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℕ, ∀ (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (a : ℤ),
      IsGE K a →
        IsGE ((etaleDerivedUpperShriek X Λ P).obj K) (a - N) :=
  sorry

/-- Étale derived upper shriek sends bounded-below derived objects to
bounded-below derived objects over a torsion coefficient ring. -/
theorem isBoundedBelow (hΛ : AddMonoid.IsTorsion Λ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory.IsBoundedBelow K →
      DerivedCategory.IsBoundedBelow ((etaleDerivedUpperShriek X Λ P).obj K) :=
  sorry

end etaleDerivedUpperShriek

end AlgebraicGeometry.Scheme.Etale

end
