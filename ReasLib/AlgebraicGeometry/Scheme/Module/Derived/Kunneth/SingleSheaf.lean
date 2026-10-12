/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory ComplexShape
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]
variable [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions
  (Limits.pullback a b).toRingedSpace.Modules]
variable [∀ G₁ G₂ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ :
  GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

variable [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toShHom a.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toShHom b.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
variable [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
variable [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]

/-- The degreewise morphism from the tensor of two degree-zero module-sheaf complexes to
the degree-zero complex on their ordinary tensor product. -/
noncomputable def tensorComponent {P : RingedSpace.{u}} (M N : P.Modules) (j : ℤ) :
    (HomologicalComplex.tensorObj
      ((CochainComplex.singleFunctor P.Modules 0).obj M)
      ((CochainComplex.singleFunctor P.Modules 0).obj N)).X j ⟶
      ((CochainComplex.singleFunctor P.Modules 0).obj (M ⊗ N)).X j :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    if hp : p = 0 then
      if hq : q = 0 then
        let hj : j = 0 :=
          h.symm.trans ((congrArg₂ (· + ·) hp hq).trans (zero_add 0))
        ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 M p hp).hom ⊗ₘ
            (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 N q hq).hom) ≫
          (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 (M ⊗ N) j hj).inv
      else 0
    else 0

/-- The degreewise tensor comparison for degree-zero module-sheaf complexes commutes with
the differentials. -/
theorem tensorComponent_comm {P : RingedSpace.{u}} (M N : P.Modules)
    (i j : ℤ) (h : (up ℤ).Rel i j) :
    tensorComponent M N i ≫
        ((CochainComplex.singleFunctor P.Modules 0).obj (M ⊗ N)).d i j =
      (HomologicalComplex.tensorObj
          ((CochainComplex.singleFunctor P.Modules 0).obj M)
          ((CochainComplex.singleFunctor P.Modules 0).obj N)).d i j ≫
        tensorComponent M N j := sorry

/-- The chain map from the tensor of two degree-zero module-sheaf complexes to the
degree-zero complex on their ordinary tensor product. -/
noncomputable def tensorComplexMap {P : RingedSpace.{u}} (M N : P.Modules) :
    HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor P.Modules 0).obj M)
        ((CochainComplex.singleFunctor P.Modules 0).obj N) ⟶
      (CochainComplex.singleFunctor P.Modules 0).obj (M ⊗ N) :=
  HomologicalComplex.Hom.mk (tensorComponent M N)
    (tensorComponent_comm M N)

/-- The total-left-derived counit comparison from derived pullback of a degree-zero module
sheaf to ordinary pullback placed in degree zero. -/
noncomputable def pullbackComparison {P Q : Scheme.{u}} (f : P ⟶ Q)
    (M : Q.Modules) :
    (RingedSpace.modulePullbackDerived f.toShHom).obj
        ((DerivedCategory.singleFunctor Q.Modules 0).obj M) ⟶
      (DerivedCategory.singleFunctor P.Modules 0).obj
        ((Scheme.Modules.pullback f).obj M) :=
  let SM := (CochainComplex.singleFunctor Q.Modules 0).obj M
  (RingedSpace.modulePullbackDerived f.toShHom).map
      ((DerivedCategory.singleFunctorIsoCompQ Q.Modules 0).hom.app M) ≫
    (RingedSpace.modulePullbackDerived f.toShHom).map
      ((DerivedCategory.quotientCompQhIso Q.Modules).inv.app SM) ≫
    ((RingedSpace.modulePullbackToDerived f.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis Q.toRingedSpace)).app
        ((HomotopyCategory.quotient Q.Modules (up ℤ)).obj SM) ≫
    (Functor.Homotopy.singleIso (RingedSpace.Hom.pullback f.toShHom) 0).hom.app M

/-- The derived-to-underived tensor comparison presented by two explicit K-flat
resolutions. -/
noncomputable def tensorComparisonOf {P : RingedSpace.{u}}
    [KFlat.HomotopyTensorDescends P]
    [KFlat.TensorDescends P]
    [KFlat.IsLocalization P]
    [∀ G₁ G₂ : GradedObject ℤ P.Modules, GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ P.Modules,
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    (M N : P.Modules) (RM RN : HomotopyCategory.KFlat P.Modules)
    (rM : RM.obj ⟶ (HomotopyCategory.quotient P.Modules (up ℤ)).obj
      ((CochainComplex.singleFunctor P.Modules 0).obj M))
    (rN : RN.obj ⟶ (HomotopyCategory.quotient P.Modules (up ℤ)).obj
      ((CochainComplex.singleFunctor P.Modules 0).obj N))
    (hrM : HomotopyCategory.quasiIso P.Modules (up ℤ) rM)
    (hrN : HomotopyCategory.quasiIso P.Modules (up ℤ) rN) :
    (DerivedCategory.singleFunctor P.Modules 0).obj M ⊗
        (DerivedCategory.singleFunctor P.Modules 0).obj N ⟶
      (DerivedCategory.singleFunctor P.Modules 0).obj (M ⊗ N) :=
  let SM := (CochainComplex.singleFunctor P.Modules 0).obj M
  let SN := (CochainComplex.singleFunctor P.Modules 0).obj N
  let q := HomotopyCategory.quotient P.Modules (up ℤ)
  let Qh : HomotopyCategory P.Modules (up ℤ) ⥤ DerivedCategory P.Modules :=
    DerivedCategory.Qh
  ((DerivedCategory.singleFunctorIsoCompQ P.Modules 0).hom.app M ⊗ₘ
      (DerivedCategory.singleFunctorIsoCompQ P.Modules 0).hom.app N) ≫
    ((DerivedCategory.quotientCompQhIso P.Modules).inv.app SM ⊗ₘ
      (DerivedCategory.quotientCompQhIso P.Modules).inv.app SN) ≫
    ((Localization.isoOfHom Qh (HomotopyCategory.quasiIso P.Modules (up ℤ)) rM
          hrM).inv ⊗ₘ
      (Localization.isoOfHom Qh (HomotopyCategory.quasiIso P.Modules (up ℤ)) rN
          hrN).inv) ≫
    (DerivedCategory.KFlat.mapTensorIso RM RN).hom ≫
    Qh.map
      ((Functor.Monoidal.μIso ((HomotopyCategory.kFlat P.Modules).ι) RM RN).inv ≫
        (rM ⊗ₘ rN) ≫ (Functor.Monoidal.μIso q SM SN).hom) ≫
    (DerivedCategory.quotientCompQhIso P.Modules).hom.app (SM ⊗ SN) ≫
    DerivedCategory.Q.map (tensorComplexMap M N) ≫
    (DerivedCategory.singleFunctorIsoCompQ P.Modules 0).inv.app (M ⊗ N)

/-- The canonical comparison from the K-flat derived tensor of two degree-zero module
sheaves to their ordinary tensor product placed in degree zero. -/
noncomputable def tensorComparison {P : RingedSpace.{u}}
    [KFlat.HomotopyTensorDescends P]
    [KFlat.TensorDescends P]
    [KFlat.IsLocalization P]
    [HomotopyCategory.KFlat.HasResolutions P.Modules]
    [∀ G₁ G₂ : GradedObject ℤ P.Modules, GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ P.Modules,
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    (M N : P.Modules) :
    (DerivedCategory.singleFunctor P.Modules 0).obj M ⊗
        (DerivedCategory.singleFunctor P.Modules 0).obj N ⟶
      (DerivedCategory.singleFunctor P.Modules 0).obj (M ⊗ N) :=
  let q := HomotopyCategory.quotient P.Modules (up ℤ)
  let RM := Classical.choice
    ((inferInstance : HomotopyCategory.KFlat.HasResolutions P.Modules)
      (q.obj ((CochainComplex.singleFunctor P.Modules 0).obj M)))
  let RN := Classical.choice
    ((inferInstance : HomotopyCategory.KFlat.HasResolutions P.Modules)
      (q.obj ((CochainComplex.singleFunctor P.Modules 0).obj N)))
  tensorComparisonOf M N RM.X₁ RN.X₁ RM.w RN.w RM.hw RN.hw

/-- The canonical degree-zero tensor comparison agrees with the comparison presented by
any pair of K-flat resolutions. -/
theorem tensorComparison_eq_of_resolutions {P : RingedSpace.{u}}
    [KFlat.HomotopyTensorDescends P]
    [KFlat.TensorDescends P]
    [KFlat.IsLocalization P]
    [HomotopyCategory.KFlat.HasResolutions P.Modules]
    [∀ G₁ G₂ : GradedObject ℤ P.Modules, GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ P.Modules,
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    (M N : P.Modules) (RM RN : HomotopyCategory.KFlat P.Modules)
    (rM : RM.obj ⟶ (HomotopyCategory.quotient P.Modules (up ℤ)).obj
      ((CochainComplex.singleFunctor P.Modules 0).obj M))
    (rN : RN.obj ⟶ (HomotopyCategory.quotient P.Modules (up ℤ)).obj
      ((CochainComplex.singleFunctor P.Modules 0).obj N))
    (hrM : HomotopyCategory.quasiIso P.Modules (up ℤ) rM)
    (hrN : HomotopyCategory.quasiIso P.Modules (up ℤ) rN) :
    tensorComparison M N =
      tensorComparisonOf M N RM RN rM rN hrM hrN := sorry

/-- The canonical comparison from the derived external tensor product of two degree-zero
module sheaves to their ordinary external tensor product placed in degree zero. -/
noncomputable def externalTensorComparison (F : X.Modules) (G : Y.Modules) :
    ModuleDerived.Kunneth.externalTensorProduct a b
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ⟶
      (DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
        (Scheme.Modules.externalTensorProduct a b F G) :=
  (pullbackComparison (Limits.pullback.fst a b) F ⊗ₘ
      pullbackComparison (Limits.pullback.snd a b) G) ≫
    tensorComparison
      ((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G)

/-- The derived-to-underived external tensor comparison is the tensor of the two pullback
comparisons followed by the degree-zero tensor comparison. -/
theorem externalTensorComparison_spec (F : X.Modules) (G : Y.Modules) :
    externalTensorComparison a b F G =
      (pullbackComparison (Limits.pullback.fst a b) F ⊗ₘ
          pullbackComparison (Limits.pullback.snd a b) G) ≫
        tensorComparison
          ((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F)
          ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G) := sorry

/-- The canonical global Künneth morphism for two module sheaves placed in degree zero. -/
noncomputable def map (F : X.Modules) (G : Y.Modules) :
    (GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward a.toShHom).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ⊗
        (GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) ⟶
      (GlobalSections.functor S.toRingedSpace).obj
        ((RingedSpace.moduleDerivedPushforward
          (Limits.pullback.fst a b ≫ a).toShHom).obj
            ((DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
              (Scheme.Modules.externalTensorProduct a b F G))) :=
  globalMap a b
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)
    ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≫
    (GlobalSections.functor S.toRingedSpace).map
      ((RingedSpace.moduleDerivedPushforward
        (Limits.pullback.fst a b ≫ a).toShHom).map
          (externalTensorComparison a b F G))

/-- The degree-zero global Künneth morphism is the derived global Künneth map followed by
derived global sections of the derived-to-underived external tensor comparison. -/
theorem map_spec (F : X.Modules) (G : Y.Modules) :
    map a b F G =
      globalMap a b
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≫
        (GlobalSections.functor S.toRingedSpace).map
          ((RingedSpace.moduleDerivedPushforward
            (Limits.pullback.fst a b ≫ a).toShHom).map
              (externalTensorComparison a b F G)) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf

end
