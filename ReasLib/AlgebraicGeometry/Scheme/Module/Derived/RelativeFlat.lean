module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction
open DerivedCategory.DerivedTensor.Bifunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeFlatComplex

variable {X S : Scheme.{u}} (a : X ⟶ S)

section ModuleProjectionFormulaMap

variable
  [KFlat.HomotopyTensorDescends
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.TensorDescends
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.IsLocalization
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.HomotopyTensorDescends S.toRingedSpace]
  [KFlat.TensorDescends S.toRingedSpace]
  [KFlat.IsLocalization S.toRingedSpace]
  [HasPair
    (RingedSpace.opensRingedSiteHom (ModuleCech.relativeSpaceMap a.toShHom))]
  [Functor.Monoidal
    (RingedSpace.modulePullbackDerived (ModuleCech.relativeSpaceMap a.toShHom))]
  [Tensor.Has (ModuleCech.relativeSpace a.toShHom)]

variable (tensorComparison :
  Tensor.functor (ModuleCech.relativeSpace a.toShHom) ≅
    MonoidalCategory.tensor
      (RingedSpace.ModuleDerived (ModuleCech.relativeSpace a.toShHom)))

/-- The canonical comparison from the module projection formula to the localization of the
ordinary tensor complex. -/
noncomputable def moduleProjectionFormulaMap
    (K : CochainComplex (ModuleCech.relativeSpace a.toShHom).Modules ℤ)
    (G : Scheme.QCoh S) :
    (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj) ⊗
        (RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) ⟶
      (RingedSpace.moduleDerivedPushforward
        (ModuleCech.relativeSpaceMap a.toShHom)).obj
          (DerivedCategory.Q.obj
            (((RingedSpace.Hom.pullback
              (ModuleCech.relativeSpaceMap a.toShHom)).mapHomologicalComplex (up ℤ)).obj
                ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj) ⊗ K)) :=
  ProjectionFormula.mate
      (ModuleCech.relativeSpaceMap a.toShHom)
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj))
      (DerivedCategory.Q.obj K) ≫
    (RingedSpace.moduleDerivedPushforward
      (ModuleCech.relativeSpaceMap a.toShHom)).map
      (tensorComparison.inv.app
          ((RingedSpace.modulePullbackDerived
              (ModuleCech.relativeSpaceMap a.toShHom)).obj
                (DerivedCategory.Q.obj
                  ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj)),
            DerivedCategory.Q.obj K) ≫
        (Tensor.functor
          (ModuleCech.relativeSpace a.toShHom)).map
          (Prod.mkHom
            ((RingedSpace.modulePullbackDerived
              (ModuleCech.relativeSpaceMap a.toShHom)).map
                ((DerivedCategory.quotientCompQhIso S.toRingedSpace.Modules).inv.app
                  ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj)) ≫
              ((RingedSpace.modulePullbackToDerived
                (ModuleCech.relativeSpaceMap a.toShHom)).totalLeftDerivedCounit
                  DerivedCategory.Qh
                  (RingedSpace.ModuleQis S.toRingedSpace)).app
                    ((HomotopyCategory.quotient S.toRingedSpace.Modules (up ℤ)).obj
                      ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj)))
            (𝟙 _)) ≫
        counitAppOfQ
          (((RingedSpace.Hom.pullback
            (ModuleCech.relativeSpaceMap a.toShHom)).mapHomologicalComplex (up ℤ)).obj
              ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj)) K)

/-- The module projection-formula comparison is the projection-formula mate followed by the
pullback and derived-tensor counits. -/
theorem moduleProjectionFormulaMap_def
    (K : CochainComplex (ModuleCech.relativeSpace a.toShHom).Modules ℤ)
    (G : Scheme.QCoh S) :
    moduleProjectionFormulaMap a tensorComparison K G =
      ProjectionFormula.mate
          (ModuleCech.relativeSpaceMap a.toShHom)
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj))
          (DerivedCategory.Q.obj K) ≫
        (RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).map
          (tensorComparison.inv.app
              ((RingedSpace.modulePullbackDerived
                  (ModuleCech.relativeSpaceMap a.toShHom)).obj
                    (DerivedCategory.Q.obj
                      ((CochainComplex.singleFunctor S.toRingedSpace.Modules 0).obj G.obj)),
                DerivedCategory.Q.obj K) ≫
            (Tensor.functor
              (ModuleCech.relativeSpace a.toShHom)).map
              (Prod.mkHom
                ((RingedSpace.modulePullbackDerived
                  (ModuleCech.relativeSpaceMap a.toShHom)).map
                    ((DerivedCategory.quotientCompQhIso S.toRingedSpace.Modules).inv.app
                      ((CochainComplex.singleFunctor
                        S.toRingedSpace.Modules 0).obj G.obj)) ≫
                  ((RingedSpace.modulePullbackToDerived
                    (ModuleCech.relativeSpaceMap a.toShHom)).totalLeftDerivedCounit
                      DerivedCategory.Qh
                      (RingedSpace.ModuleQis S.toRingedSpace)).app
                        ((HomotopyCategory.quotient
                          S.toRingedSpace.Modules (up ℤ)).obj
                            ((CochainComplex.singleFunctor
                              S.toRingedSpace.Modules 0).obj G.obj)))
                (𝟙 _)) ≫
            counitAppOfQ
              (((RingedSpace.Hom.pullback
                (ModuleCech.relativeSpaceMap a.toShHom)).mapHomologicalComplex (up ℤ)).obj
                  ((CochainComplex.singleFunctor
                    S.toRingedSpace.Modules 0).obj G.obj)) K) := sorry

end ModuleProjectionFormulaMap

variable [h_quasiCompact : AlgebraicGeometry.QuasiCompact a]
variable [h_quasiSeparated : AlgebraicGeometry.QuasiSeparated a]
variable (F : ℤ → Scheme.QCoh X)
variable (K : CochainComplex (ModuleCech.relativeSpace a.toShHom).Modules ℤ)
variable (termIso : ∀ n, K.X n ≅ SheafOfModules.relativeModule (F n).obj a.toShHom)
variable (hFlat : ∀ n, SheafOfModules.IsFlatOver (F n).obj a.toShHom)
variable (hBoundedAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
variable (hBoundedBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)

include h_quasiCompact h_quasiSeparated termIso hFlat hBoundedAbove hBoundedBelow

/-- The derived pushforward of a locally bounded coefficient-linear complex with relatively
flat quasicoherent terms is locally bounded above and below. -/
theorem pushforward_isLocallyBounded :
    RingedSpace.ModuleDerived.IsLocallyBoundedAbove
        ((RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) ∧
      RingedSpace.ModuleDerived.IsLocallyBoundedBelow
        ((RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) := sorry

/-- The derived pushforward of a locally bounded coefficient-linear complex with relatively
flat quasicoherent terms has quasicoherent cohomology. -/
theorem pushforward_mem_derivedQuasiCoherent :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty S.toRingedSpace)
      ((RingedSpace.moduleDerivedPushforward
        (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) := sorry

/-- The derived pushforward of a locally bounded coefficient-linear complex with relatively
flat quasicoherent terms locally has finite Tor dimension. -/
theorem pushforward_locallyHasFiniteTorDimension
    [∀ U : TopologicalSpace.Opens (S.toRingedSpace).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules ((S.toRingedSpace).restrict U.isOpenEmbedding))]
    :
    LocallyHasFiniteTorDimension
      ((RingedSpace.moduleDerivedPushforward
        (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) := sorry

section ProjectionFormula

variable
  [KFlat.HomotopyTensorDescends
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.TensorDescends
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.IsLocalization
    (ModuleCech.relativeSpace a.toShHom)]
  [KFlat.HomotopyTensorDescends S.toRingedSpace]
  [KFlat.TensorDescends S.toRingedSpace]
  [KFlat.IsLocalization S.toRingedSpace]
  [HasPair
    (RingedSpace.opensRingedSiteHom (ModuleCech.relativeSpaceMap a.toShHom))]
  [Functor.Monoidal
    (RingedSpace.modulePullbackDerived (ModuleCech.relativeSpaceMap a.toShHom))]

/-- The canonical derived projection-formula map is invertible for every base complex with
quasicoherent cohomology. -/
theorem projectionFormula
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty S.toRingedSpace)) :
    IsIso
      (ProjectionFormula.mate
        (ModuleCech.relativeSpaceMap a.toShHom) L.obj (DerivedCategory.Q.obj K)) := sorry

/-- For a quasicoherent module, the canonical module projection-formula map to the derived
pushforward of the ordinary tensor complex is invertible. -/
theorem moduleProjectionFormula
    [Tensor.Has (ModuleCech.relativeSpace a.toShHom)]
    (tensorComparison :
      Tensor.functor (ModuleCech.relativeSpace a.toShHom) ≅
        MonoidalCategory.tensor
          (RingedSpace.ModuleDerived (ModuleCech.relativeSpace a.toShHom)))
    (G : Scheme.QCoh S) :
    IsIso (moduleProjectionFormulaMap a tensorComparison K G) := sorry

end ProjectionFormula

end AlgebraicGeometry.Scheme.RelativeFlatComplex
