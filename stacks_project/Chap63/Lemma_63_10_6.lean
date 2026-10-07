module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

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
variable [IsSeparated X'.hom] [Scheme.Hom.FiniteType X'.hom]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsThickening i]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
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

/-- Lemma 63.10.6 (1): if `f' = X'.hom` is a finite type separated morphism of
quasi-compact quasi-separated schemes, `i : X.left ⟶ X'.left` is a thickening,
and `f = f' ∘ i` (equivalently `i ≫ X'.hom = X.hom`), then for `K'` in
`D⁺_tors(X'_étale, Λ)` the object `Rf_!(i⁻¹ K')` is isomorphic in
`D(Y_étale, Λ)` to `Rf'_! K'`, where `Rf_!` is `etaleDerivedLowerShriek X P`
and `Rf'_!` is `etaleDerivedLowerShriek X' P'`. -/
@[stacks 0GKQ]
theorem etaleDerivedLowerShriek_inverseImage_thickening
    (h_comp : i ≫ X'.hom = X.hom)
    (K' : EtaleDerived X'.left Λ) (h_tors : etaleDerivedIsTorsion K')
    (n : ℤ) [DerivedCategory.IsGE K' n] :
    IsIsomorphic
      ((etaleDerivedLowerShriek X P).obj
        (((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
            X'.left.smallEtaleTopology X.left.smallEtaleTopology).mapDerivedCategory.obj
          K'))
      ((etaleDerivedLowerShriek X' P').obj K') :=
  sorry

/-- Lemma 63.10.6 (2): if in addition `Λ` is a torsion ring, then
`Rf_! ∘ i⁻¹` is isomorphic to `Rf'_!` as functors
`D(X'_étale, Λ) ⥤ D(Y_étale, Λ)`. -/
@[stacks 0GKQ]
theorem etaleDerivedLowerShriek_inverseImage_thickening_of_isTorsion
    (h_comp : i ≫ X'.hom = X.hom) (hΛ : AddMonoid.IsTorsion Λ) :
    IsIsomorphic
      (((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
          X'.left.smallEtaleTopology X.left.smallEtaleTopology).mapDerivedCategory ⋙
        etaleDerivedLowerShriek X P)
      (etaleDerivedLowerShriek X' P') :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
