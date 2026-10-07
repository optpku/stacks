module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»
public import stacks_project.Chap63.Remark_63_10_9

/-!
# Sheafy trace for derived étale lower/upper shriek

The source morphism
`Rf_* RHom_Λ(L, Rf^! K) ⟶ RHom_Λ(Rf_! L, K)`
is the compactification internal-Hom comparison of `Rf_!` followed by
`RHom(Rf_! L, ε_K)` for the counit `ε` of `Rf_! ⊣ Rf^!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y)
    (smallEtaleTopology (Over.left P.obj.right))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleRestrictionSheaf (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).Additive]
variable [PreservesFiniteLimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [PreservesFiniteColimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).PreservesInjectiveObjects]
variable [(ExactFunctor.of
    (etaleModulePushforward (Compactification.Of.ι P) Λ)).obj.PreservesInjectiveObjects]
variable [(etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward X.hom Λ).Additive]
variable [(etaleModulePushforward
    (Compactification.Of.ι P ≫ Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
    etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
      etaleModulePushforward (Over.hom P.obj.right) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [MonoidalCategory (EtaleDerived X.left Λ)]
variable [MonoidalClosed (EtaleDerived X.left Λ)]
variable [MonoidalCategory (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalClosed (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalCategory (EtaleDerived Y Λ)]
variable [MonoidalClosed (EtaleDerived Y Λ)]
variable [(etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).OplaxMonoidal]
variable [(etaleDerivedExtensionByZeroAdjunction
    (Compactification.Of.ι P) Λ).ProjectionFormulaMap]
variable [(etaleDerivedPushforward (Over.hom P.obj.right) :
    EtaleDerived (Over.left P.obj.right) Λ ⥤ EtaleDerived Y Λ).LaxMonoidal]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

/-- The sheafy-trace morphism
`Rf_* RHom_Λ(L, Rf^! K) ⟶ RHom_Λ(Rf_! L, K)`. -/
def etaleDerivedSheafyTrace
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    (etaleDerivedPushforward X.hom).obj
      ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ⟶
    (ihom ((etaleDerivedLowerShriek X P).obj L)).obj K :=
  etaleDerivedLowerShriekInternalHom X P L
      ((etaleDerivedUpperShriek X Λ P).obj K) ≫
    (ihom ((etaleDerivedLowerShriek X P).obj L)).map
      ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K)

/-- The sheafy-trace morphism is the internal-Hom comparison at
`(L, Rf^! K)` followed by the counit of `Rf_! ⊣ Rf^!`. -/
theorem etaleDerivedSheafyTrace_eq
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    etaleDerivedSheafyTrace X P L K =
      etaleDerivedLowerShriekInternalHom X P L
          ((etaleDerivedUpperShriek X Λ P).obj K) ≫
        (ihom ((etaleDerivedLowerShriek X P).obj L)).map
          ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K) :=
  sorry

/-- The sheafy-trace morphism is natural in the source object `L`. -/
theorem etaleDerivedSheafyTrace_natural_left
    {L L' : EtaleDerived X.left Λ} (f : L ⟶ L') (K : EtaleDerived Y Λ) :
    (etaleDerivedPushforward X.hom).map
          ((MonoidalClosed.pre f).app ((etaleDerivedUpperShriek X Λ P).obj K)) ≫
        etaleDerivedSheafyTrace X P L K =
      etaleDerivedSheafyTrace X P L' K ≫
        (MonoidalClosed.pre ((etaleDerivedLowerShriek X P).map f)).app K :=
  sorry

/-- The sheafy-trace morphism is natural in the target object `K`. -/
theorem etaleDerivedSheafyTrace_natural_right
    (L : EtaleDerived X.left Λ) {K K' : EtaleDerived Y Λ} (g : K ⟶ K') :
    (etaleDerivedPushforward X.hom).map
          ((ihom L).map ((etaleDerivedUpperShriek X Λ P).map g)) ≫
        etaleDerivedSheafyTrace X P L K' =
      etaleDerivedSheafyTrace X P L K ≫
        (ihom ((etaleDerivedLowerShriek X P).obj L)).map g :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
