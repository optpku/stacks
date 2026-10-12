/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
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
variable [MonoidalCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalPreadditive (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ (K L : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
      (ComplexShape.up ℤ)]
variable [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (ComplexShape.up ℤ)]
variable [hXTensor :
    @DerivedTensor.Right.Has (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) _ _ _ _ _ _]
variable [hYTensor :
    @DerivedTensor.Right.Has (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _ _ _ _ _ _]
variable [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback X.hom).sheafPullback
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback X.hom).sheafPullback
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback X.hom).sheafPullback
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology)]

/-- Lemma 63.10.7: if `f = X.hom` is a separated finite type morphism of
quasi-compact quasi-separated schemes and `Λ` is a torsion ring, then for
`E` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`,
`Rf_! E ⊗ᴸ K` is isomorphic in `D(Y_étale, Λ)` to
`Rf_!(E ⊗ᴸ f⁻¹ K)`, where `Rf_!` is `etaleDerivedLowerShriek X P`. -/
@[stacks 0GL5]
theorem etaleDerivedLowerShriek_tensor_inverseImage
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    IsIsomorphic
      ((etaleDerivedLowerShriek X P).obj E ⊗ᴸ K)
      ((etaleDerivedLowerShriek X P).obj
        (E ⊗ᴸ
          ((smallEtalePullback X.hom).sheafPullback
              (ModuleCat.{u} Λ) Y.smallEtaleTopology
              X.left.smallEtaleTopology).mapDerivedCategory.obj
            K)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
