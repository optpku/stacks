module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_3_13_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_3_ExtensionByZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal-Hom comparison for derived étale lower shriek

For a compactification `f = f̄ ∘ j` of a separated finite-type morphism, the
canonical morphism `α : Rf_* RHom_Λ(K, L) ⟶ RHom_Λ(Rf_! K, Rf_! L)` is
`γ ∘ R f̄_* β` after Leray, with `β` the curry of interior evaluation after
the mixed `j_!` projection formula and `γ` the lax-monoidal internal-Hom
comparison of `R f̄_*`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open RightDerived.Cochain
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ]

/-- Underived composition of small-étale module pushforwards along a pair of
scheme morphisms. -/
def etaleModulePushforwardCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ ≅
      etaleModulePushforward (f ≫ g) Λ :=
  sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g)
    (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology
    X.smallEtaleTopology

/-- Transport of underived module pushforward along an equality of scheme
morphisms. -/
def etaleModulePushforwardCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    etaleModulePushforward f Λ ≅ etaleModulePushforward g Λ :=
  eqToIso (congrArg (fun u ↦ etaleModulePushforward u Λ) h)

/-- `etaleModulePushforwardCongr` is `eqToIso` of `etaleModulePushforward`. -/
theorem etaleModulePushforwardCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    etaleModulePushforwardCongr h =
      eqToIso (congrArg (fun u ↦ etaleModulePushforward u Λ) h) :=
  sorry

/-- The composition isomorphism of module pushforwards is continuous sheaf
pushforward along `smallEtalePullbackCompIso`. -/
theorem etaleModulePushforwardCompIso_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModulePushforwardCompIso f g =
      sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g)
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology
        X.smallEtaleTopology :=
  sorry

variable {Y : Scheme.{u}} (X : Over Y)
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

/-- Site-level adjunction `etaleRestriction ⊣ smallEtalePullback` along the
compactification interior. -/
def etaleInteriorSiteAdjunction :
    etaleRestriction (Compactification.Of.ι P) ⊣
      smallEtalePullback (Compactification.Of.ι P) :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤
    (Compactification.Of.ι P) inferInstance trivial

/-- The interior site adjunction is `Over.mapPullbackAdj` for étale morphisms. -/
theorem etaleInteriorSiteAdjunction_eq :
    etaleInteriorSiteAdjunction X P =
      MorphismProperty.Over.mapPullbackAdj @Etale ⊤
        (Compactification.Of.ι P) inferInstance trivial :=
  sorry

/-- Sheaf-level adjunction `j⁻¹ ⊣ j_*` of `Λ`-modules along the interior
immersion. -/
def etaleInteriorSheafPushforwardAdjunction :
    etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⊣
      etaleModulePushforward (Compactification.Of.ι P) Λ :=
  Adjunction.sheafPushforwardContinuous (etaleInteriorSiteAdjunction X P)
    (smallEtaleTopology X.left) (smallEtaleTopology (Over.left P.obj.right))

/-- Sheaf-level interior pushforward is continuous sheaf pushforward of the
site adjunction. -/
theorem etaleInteriorSheafPushforwardAdjunction_eq :
    etaleInteriorSheafPushforwardAdjunction X P =
      (Adjunction.sheafPushforwardContinuous (etaleInteriorSiteAdjunction X P)
        (smallEtaleTopology X.left) (smallEtaleTopology (Over.left P.obj.right)) :
        etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⊣
          etaleModulePushforward (Compactification.Of.ι P) Λ) :=
  sorry

/-- Derived interior pushforward `Rj_*` along the compactification immersion. -/
abbrev etaleDerivedInteriorPushforward :
    EtaleDerived X.left Λ ⥤ EtaleDerived (Over.left P.obj.right) Λ :=
  (etaleModulePushforward (Compactification.Of.ι P) Λ).mapDerivedCategory

/-- Derived interior pushforward is `mapDerivedCategory` of module
pushforward along `j`. -/
theorem etaleDerivedInteriorPushforward_def :
    etaleDerivedInteriorPushforward X P =
      (etaleModulePushforward (Compactification.Of.ι P) Λ).mapDerivedCategory :=
  sorry

/-- The adjunction `j⁻¹ ⊣ Rj_*` on unbounded derived categories. -/
def etaleDerivedInteriorPushforwardAdjunction :
    etaleDerivedRestriction (Compactification.Of.ι P) Λ ⊣
      etaleDerivedInteriorPushforward X P :=
  Adjunction.mapDerivedCategory (etaleInteriorSheafPushforwardAdjunction X P)

/-- Derived interior pushforward adjunction is `mapDerivedCategory` of the
sheaf-level adjunction. -/
theorem etaleDerivedInteriorPushforwardAdjunction_eq :
    etaleDerivedInteriorPushforwardAdjunction X P =
      (Adjunction.mapDerivedCategory
        (etaleInteriorSheafPushforwardAdjunction X P) :
        etaleDerivedRestriction (Compactification.Of.ι P) Λ ⊣
          etaleDerivedInteriorPushforward X P) :=
  sorry

/-- Uncurried evaluation of `j_!` of internal Hom after the mixed projection
formula `j_! A ⊗ Rj_* I ⟶ j_!(A ⊗ j⁻¹ Rj_* I)`. -/
def etaleDerivedInteriorInternalHomEval
    (A B : EtaleDerived X.left Λ) :
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A ⊗
      (etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B) ⟶
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B :=
  (etaleDerivedExtensionByZeroAdjunction
      (Compactification.Of.ι P) Λ).projectionFormulaMapInv A
      ((etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B)) ≫
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).map
      ((𝟙 A ⊗ₘ (etaleDerivedInteriorPushforwardAdjunction X P).counit.app
          ((ihom A).obj B)) ≫
        (ihom.ev A).app B)

/-- Interior evaluation is the mixed projection formula followed by `j_!` of
`(id ⊗ counit) ≫ ev`. -/
theorem etaleDerivedInteriorInternalHomEval_eq
    (A B : EtaleDerived X.left Λ) :
    etaleDerivedInteriorInternalHomEval X P A B =
      (etaleDerivedExtensionByZeroAdjunction
          (Compactification.Of.ι P) Λ).projectionFormulaMapInv A
          ((etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B)) ≫
        (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).map
          ((𝟙 A ⊗ₘ (etaleDerivedInteriorPushforwardAdjunction X P).counit.app
              ((ihom A).obj B)) ≫
            (ihom.ev A).app B) :=
  sorry

/-- The interior internal-Hom comparison
`Rj_* RHom(A, B) ⟶ RHom(j_! A, j_! B)`. -/
def etaleDerivedInteriorInternalHom
    (A B : EtaleDerived X.left Λ) :
    (etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)).obj
        ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B) :=
  MonoidalClosed.curry (etaleDerivedInteriorInternalHomEval X P A B)

/-- Interior internal Hom is the curry of interior evaluation. -/
theorem etaleDerivedInteriorInternalHom_eq
    (A B : EtaleDerived X.left Λ) :
    etaleDerivedInteriorInternalHom X P A B =
      MonoidalClosed.curry (etaleDerivedInteriorInternalHomEval X P A B) :=
  sorry

/-- The compactification pushforward internal-Hom comparison
`R f̄_* RHom(A, B) ⟶ RHom(R f̄_* A, R f̄_* B)`. -/
def etaleDerivedCompactificationPushforwardInternalHom
    (A B : EtaleDerived (Over.left P.obj.right) Λ) :
    (etaleDerivedPushforward (Over.hom P.obj.right)).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedPushforward (Over.hom P.obj.right)).obj A)).obj
        ((etaleDerivedPushforward (Over.hom P.obj.right)).obj B) :=
  LaxMonoidal.InternalHom.comparison
    (etaleDerivedPushforward (Over.hom P.obj.right)) A B

/-- Compactification internal Hom is the lax-monoidal comparison of `R f̄_*`. -/
theorem etaleDerivedCompactificationPushforwardInternalHom_eq
    (A B : EtaleDerived (Over.left P.obj.right) Λ) :
    etaleDerivedCompactificationPushforwardInternalHom X P A B =
      LaxMonoidal.InternalHom.comparison
        (etaleDerivedPushforward (Over.hom P.obj.right)) A B :=
  sorry

/-- Underived Leray identification `f_* ≅ f̄_* ∘ j_*` along the
compactification triangle. -/
def etaleModulePushforwardLerayIso :
    etaleModulePushforward X.hom Λ ≅
      etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
        etaleModulePushforward (Over.hom P.obj.right) Λ :=
  etaleModulePushforwardCongr (Over.w P.obj.hom).symm ≪≫
    (etaleModulePushforwardCompIso (Compactification.Of.ι P)
      (Over.hom P.obj.right)).symm

/-- The underived Leray isomorphism is transport along `X.hom = j ≫ f̄`
followed by the composition isomorphism. -/
theorem etaleModulePushforwardLerayIso_eq :
    etaleModulePushforwardLerayIso X P =
      (etaleModulePushforwardCongr (Over.w P.obj.hom).symm ≪≫
        (etaleModulePushforwardCompIso (Compactification.Of.ι P)
          (Over.hom P.obj.right)).symm :
        etaleModulePushforward X.hom Λ ≅
          etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
            etaleModulePushforward (Over.hom P.obj.right) Λ) :=
  sorry

/-- Leray comparison identifying `Rf_*` with `R f̄_* ∘ Rj_*` along the
compactification factorization `X.hom = j ≫ f̄`. -/
def etaleDerivedPushforwardLeray :
    (etaleDerivedPushforward X.hom :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
      etaleDerivedInteriorPushforward X P ⋙
        (etaleDerivedPushforward (Over.hom P.obj.right) :
          EtaleDerived (Over.left P.obj.right) Λ ⥤ EtaleDerived Y Λ) :=
  (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived X.left Λ)
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit (etaleModulePushforward X.hom Λ))
      (RightDerived.Cochain.unit
        (etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
          etaleModulePushforward (Over.hom P.obj.right) Λ))
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (etaleModulePushforwardLerayIso X P) (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived Y Λ))).hom ≫
    (ExactFirst.iso
        (ExactFunctor.of
          (etaleModulePushforward (Compactification.Of.ι P) Λ))
        (etaleModulePushforward (Over.hom P.obj.right) Λ)).inv

/-- Leray is natural in objects of `D(X_étale, Λ)`. -/
theorem etaleDerivedPushforwardLeray_naturality
    {K L : EtaleDerived X.left Λ} (f : K ⟶ L) :
    (etaleDerivedPushforward X.hom).map f ≫
        (etaleDerivedPushforwardLeray X P).app L =
      (etaleDerivedPushforwardLeray X P).app K ≫
        (etaleDerivedInteriorPushforward X P ⋙
            etaleDerivedPushforward (Over.hom P.obj.right)).map f :=
  sorry

/-- Remark 63.10.9: for a separated finite-type morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes, a torsion coefficient ring `Λ`, and
objects `K`, `L` of `D(X_étale, Λ)`, there is a canonical map
`α : Rf_* RHom_Λ(K, L) ⟶ RHom_Λ(Rf_! K, Rf_! L)`, functorial in `K` and `L`,
obtained from a compactification `f = f̄ ∘ j` as
`α = γ ∘ R f̄_* β` after Leray `Rf_* = R f̄_* ∘ Rj_*`. -/
@[stacks 0GL7]
def etaleDerivedLowerShriekInternalHom
    (A B : EtaleDerived X.left Λ) :
    (etaleDerivedPushforward X.hom).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedLowerShriek X P).obj A)).obj
        ((etaleDerivedLowerShriek X P).obj B) :=
  (etaleDerivedPushforwardLeray X P).app ((ihom A).obj B) ≫
    (etaleDerivedPushforward (Over.hom P.obj.right)).map
      (etaleDerivedInteriorInternalHom X P A B) ≫
    etaleDerivedCompactificationPushforwardInternalHom X P
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B)

/-- The mixed internal-Hom comparison is `R f̄_* β ≫ γ` after Leray. -/
theorem etaleDerivedLowerShriekInternalHom_eq
    (A B : EtaleDerived X.left Λ) :
    etaleDerivedLowerShriekInternalHom X P A B =
      (etaleDerivedPushforwardLeray X P).app ((ihom A).obj B) ≫
        (etaleDerivedPushforward (Over.hom P.obj.right)).map
          (etaleDerivedInteriorInternalHom X P A B) ≫
        etaleDerivedCompactificationPushforwardInternalHom X P
          ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)
          ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
