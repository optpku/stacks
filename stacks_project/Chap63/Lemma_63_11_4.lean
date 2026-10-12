/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Bounds
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»
import Mathlib.Tactic.CrossRefAttribute

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
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

namespace etaleDerivedUpperShriek

/-- Lemma 63.11.4: for a finite type separated morphism `X.hom : X.left ⟶ Y` of
quasi-compact quasi-separated schemes and a torsion ring `Λ`, the functor
`Rf^! = etaleDerivedUpperShriek X Λ P` sends `D⁺(Y_étale, Λ)` into
`D⁺(X_étale, Λ)`. More precisely, there exists `N : ℕ` such that
`Functor.TStructure.MapsGE (etaleDerivedUpperShriek X Λ P) t t (-(N : ℤ))`:
`IsGE K a` implies `IsGE ((etaleDerivedUpperShriek X Λ P).obj K) (a - N)`. -/
@[stacks 0GLA]
theorem exists_mapsGE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℕ, Functor.TStructure.MapsGE (etaleDerivedUpperShriek X Λ P) t t
      (-(N : ℤ)) :=
  sorry

/-- Objectwise form of the lower t-structure bound for `etaleDerivedUpperShriek`:
there exists `N : ℕ` such that `IsGE K a` implies
`IsGE ((etaleDerivedUpperShriek X Λ P).obj K) (a - N)`. -/
theorem exists_isGE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℕ, ∀ (K : EtaleDerived Y Λ) (a : ℤ),
      IsGE K a →
        IsGE ((etaleDerivedUpperShriek X Λ P).obj K) (a - N) :=
  sorry

/-- The functor `etaleDerivedUpperShriek X Λ P` sends bounded-below objects of
`EtaleDerived Y Λ` to bounded-below objects of `EtaleDerived X.left Λ`. -/
theorem isBoundedBelow (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y Λ) :
    DerivedCategory.IsBoundedBelow K →
      DerivedCategory.IsBoundedBelow ((etaleDerivedUpperShriek X Λ P).obj K) :=
  sorry

end etaleDerivedUpperShriek

end AlgebraicGeometry.Scheme.Etale

end
