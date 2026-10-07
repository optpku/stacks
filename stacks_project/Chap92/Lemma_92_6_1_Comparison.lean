module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.InverseImage
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap92.«92_6_0_2_Site»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-tensor comparison for a commutative square of rings

A commutative square of rings induces an underived `A'`-module map `B ⊗[A] A' ⟶ B'` and a
canonical morphism `B ⊗[A]^L A' ⟶ B'[0]` in `D(A')`. Invertibility of that morphism is the
hypothesis of Stacks Lemma 92.6.1, which then makes the derived-colimit comparison
`Lπ_! ∘ g⁻¹ ⇒ Lπ'_!` an isomorphism on `D(Ab)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory
open scoped TensorProduct
open Algebra.TensorProduct
open scoped Algebra.TensorProduct.Right

noncomputable section

universe u q q' t

namespace RingedSite.Cotangent.Functoriality

variable {A A' B B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/-- The `A`-module `B` induced by a ring homomorphism `α : A ⟶ B`. -/
abbrev moduleCatOfHom (α : A ⟶ B) : ModuleCat.{u} A :=
  @ModuleCat.of (A : Type u) _ (B : Type u) _ (algebraOfHom α).toModule

/-- Unfolding `moduleCatOfHom` recovers `ModuleCat.of` for `algebraOfHom`. -/
theorem moduleCatOfHom_eq (α : A ⟶ B) :
    moduleCatOfHom α = @ModuleCat.of (A : Type u) _ (B : Type u) _ (algebraOfHom α).toModule :=
  sorry

/-- The tensor product `B ⊗[A] A'` determined by the left and top arrows of a ring square. -/
abbrev tensorCarrier (α : A ⟶ B) (ρ : A ⟶ A') : Type u :=
  @TensorProduct (A : Type u) _ (B : Type u) (A' : Type u) _ _
    (algebraOfHom α).toModule (algebraOfHom ρ).toModule

/-- The `A'`-module structure on `B ⊗[A] A'` via the right tensor factor. -/
abbrev tensorCarrierModule (α : A ⟶ B) (ρ : A ⟶ A') :
    Module (A' : Type u) (tensorCarrier α ρ) :=
  @Algebra.toModule (A' : Type u) (tensorCarrier α ρ) _ _
    (@rightAlgebra (A : Type u) (B : Type u) (A' : Type u) _ _
      (algebraOfHom α) _ (algebraOfHom ρ))

/-- The `A'`-module `B ⊗[A] A'` induced by a pair of ring maps out of `A`. -/
abbrev tensorModuleCat (α : A ⟶ B) (ρ : A ⟶ A') : ModuleCat.{u} A' :=
  @ModuleCat.of (A' : Type u) _ (tensorCarrier α ρ) _ (tensorCarrierModule α ρ)

/-- Unfolding `tensorModuleCat` recovers `ModuleCat.of` of the right tensor product. -/
theorem tensorModuleCat_eq (α : A ⟶ B) (ρ : A ⟶ A') :
    tensorModuleCat α ρ =
      @ModuleCat.of (A' : Type u) _ (tensorCarrier α ρ) _ (tensorCarrierModule α ρ) :=
  sorry

/-- The `A'`-linear map underlying `tensorCompare`. -/
noncomputable def tensorCompareLinearMap (sq : CommSq ρ α β φ) :
    @LinearMap (A' : Type u) (A' : Type u) _ _ (RingHom.id _)
      (tensorCarrier α ρ) (B' : Type u) _ _ (tensorCarrierModule α ρ)
      (algebraOfHom β).toModule :=
  @LinearMap.mk (A' : Type u) (A' : Type u) _ _ (RingHom.id _)
    (tensorCarrier α ρ) (B' : Type u) _ _ (tensorCarrierModule α ρ)
    (algebraOfHom β).toModule
    (@AddHom.mk (tensorCarrier α ρ) (B' : Type u) _ _ (tensorCompare sq) sorry) sorry

/-- The underived `A'`-module comparison `B ⊗[A] A' ⟶ B'` induced by a commutative square of
rings. -/
noncomputable def tensorCompareModuleHom (sq : CommSq ρ α β φ) :
    tensorModuleCat α ρ ⟶ moduleCatOfHom β :=
  @ModuleCat.ofHom (A' : Type u) _ (tensorCarrier α ρ) (B' : Type u) _
    (tensorCarrierModule α ρ) _ (algebraOfHom β).toModule (tensorCompareLinearMap sq)

/-- Evaluating `tensorCompareModuleHom` recovers `tensorCompare`. -/
theorem tensorCompareModuleHom_apply (sq : CommSq ρ α β φ) (x : tensorCarrier α ρ) :
    (tensorCompareModuleHom sq).hom x = tensorCompare sq x :=
  sorry

/-- The left tensor product `A' ⊗[A] B` determined by the left and top arrows of a ring square. -/
abbrev tensorLeftCarrier (α : A ⟶ B) (ρ : A ⟶ A') : Type u :=
  @TensorProduct (A : Type u) _ (A' : Type u) (B : Type u) _ _
    (algebraOfHom ρ).toModule (algebraOfHom α).toModule

/-- The comparison from categorical scalar extension of `B` along `ρ` to `B ⊗[A] A'`. -/
noncomputable def extendScalarsToTensor (α : A ⟶ B) (ρ : A ⟶ A') :
    (ModuleCat.extendScalars ρ.hom).obj (moduleCatOfHom α) ⟶ tensorModuleCat α ρ :=
  (@ModuleCat.ExtendScalars.tensorIso (A : Type u) (A' : Type u) _ _ (algebraOfHom ρ)
      (moduleCatOfHom α)).hom ≫
    @ModuleCat.ofHom (A' : Type u) _ (tensorLeftCarrier α ρ) (tensorCarrier α ρ) _ _ _
      (tensorCarrierModule α ρ)
      (@commRight (A : Type u) (A' : Type u) (B : Type u) _ _ (algebraOfHom ρ) _
        (algebraOfHom α)).toLinearMap

/-- The canonical morphism `B ⊗[A]^L A' ⟶ B'[0]` in `D(A')` induced by a commutative square of
rings. -/
noncomputable def derivedTensorCompare (sq : CommSq ρ α β φ) :
    (ModuleCat.derivedExtensionOfScalars ρ.hom).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (moduleCatOfHom α)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A') (0 : ℤ)).obj (moduleCatOfHom β) :=
  (ModuleCat.derivedExtensionOfScalars ρ.hom).map
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) (0 : ℤ)).hom.app
        (moduleCatOfHom α)) ≫
    (ModuleCat.derivedExtensionComplexCounit ρ.hom).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (moduleCatOfHom α)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars ρ.hom) (up ℤ) (0 : ℤ)).hom.app (moduleCatOfHom α)) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A') (0 : ℤ)).inv.app
      ((ModuleCat.extendScalars ρ.hom).obj (moduleCatOfHom α)) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A') (0 : ℤ)).map
      (extendScalarsToTensor α ρ ≫ tensorCompareModuleHom sq)

/-- Unfolding `derivedTensorCompare` recovers the counit-identification-tensorCompare composite. -/
theorem derivedTensorCompare_eq (sq : CommSq ρ α β φ) :
    derivedTensorCompare sq =
      (ModuleCat.derivedExtensionOfScalars ρ.hom).map
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) (0 : ℤ)).hom.app
            (moduleCatOfHom α)) ≫
        (ModuleCat.derivedExtensionComplexCounit ρ.hom).app
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (moduleCatOfHom α)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.extendScalars ρ.hom) (up ℤ) (0 : ℤ)).hom.app (moduleCatOfHom α)) ≫
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A') (0 : ℤ)).inv.app
          ((ModuleCat.extendScalars ρ.hom).obj (moduleCatOfHom α)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A') (0 : ℤ)).map
          (extendScalarsToTensor α ρ ≫ tensorCompareModuleHom sq) :=
  sorry

/-- A commutative square of rings induces a quasi-isomorphism `B ⊗[A]^L A' = B'` when the
canonical derived comparison is an isomorphism in `D(A')`. -/
def InducesDerivedTensorQuasiIso (sq : CommSq ρ α β φ) : Prop :=
  IsIso (derivedTensorCompare sq)

/-- The induced derived-tensor quasi-isomorphism unpacks as Tor-independence of `B` and `A'`
together with invertibility of the underived comparison. -/
theorem inducesDerivedTensorQuasiIso_iff (sq : CommSq ρ α β φ) :
    InducesDerivedTensorQuasiIso sq ↔
      ModuleCat.Tor.IsIndependent (moduleCatOfHom α) (moduleCatOfHom ρ) ∧
        IsIso (tensorCompareModuleHom sq) :=
  sorry

variable [HasColimitsOfShape (polynomialSite α)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (polynomialSite β)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((polynomialSite α)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (polynomialSite α) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((polynomialSite α)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (polynomialSite β) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℤ))]

/-- If a commutative square of rings induces a quasi-isomorphism `B ⊗[A]^L A' = B'`, then the
canonical comparison `Lπ_! ∘ g⁻¹ ⇒ Lπ'_!` is an isomorphism on `D(Ab)`. Here `g⁻¹` is
`presheafInverseImage (mapOp sq)`. -/
theorem inverseImageComparison_isIso (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq) :
    IsIso (DerivedColimit.inverseImageComparison AddCommGrpCat.{u} (mapOp sq)) :=
  sorry

/-- If a commutative square of rings induces a quasi-isomorphism `B ⊗[A]^L A' = B'`, then
`Lπ_! ∘ g⁻¹` and `Lπ'_!` agree on the heart of `D(Ab(C'))`. -/
theorem inverseImage_lowerShriek (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (mapOp sq) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![(polynomialSite α), AddCommGrpCat.{u}])
      ((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(polynomialSite β), AddCommGrpCat.{u}]) :=
  sorry

/-- Objectwise form of `Lπ_!(g⁻¹ F') = Lπ'_!(F')` in `D(Ab)`. -/
theorem inverseImage_lowerShriek_obj (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq)
    (F' : (polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (mapOp sq) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![(polynomialSite α), AddCommGrpCat.{u}]).obj F')
      (((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(polynomialSite β), AddCommGrpCat.{u}]).obj F') :=
  sorry

end RingedSite.Cotangent.Functoriality

