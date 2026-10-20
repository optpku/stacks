module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RelativeFlat
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived
open DerivedCategory.DerivedTensor.Bifunctor

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeFlatComplex

variable {X S : Scheme.{u}} (a : X ⟶ S)
variable [h_quasiCompact : AlgebraicGeometry.QuasiCompact a]
variable [h_quasiSeparated : AlgebraicGeometry.QuasiSeparated a]
variable (F : ℤ → Scheme.QCoh X)
variable (K : CochainComplex (ModuleCech.relativeSpace a.toShHom).Modules ℤ)
variable (termIso : ∀ n, K.X n ≅ SheafOfModules.relativeModule (F n).obj a.toShHom)
variable (hFlat : ∀ n, SheafOfModules.IsFlatOver (F n).obj a.toShHom)
variable (hBoundedAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
variable (hBoundedBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)

/- Lemma 36.23.2 (1): the derived pushforward of a locally bounded coefficient-linear
complex with relatively flat quasicoherent terms is locally bounded. -/
@[stacks 0FML] #check
  (AlgebraicGeometry.Scheme.RelativeFlatComplex.pushforward_isLocallyBounded
    a F K termIso hFlat hBoundedAbove hBoundedBelow :
      RingedSpace.ModuleDerived.IsLocallyBoundedAbove
          ((RingedSpace.moduleDerivedPushforward
            (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)) ∧
        RingedSpace.ModuleDerived.IsLocallyBoundedBelow
          ((RingedSpace.moduleDerivedPushforward
            (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)))

/- Lemma 36.23.2 (2): the derived pushforward has quasicoherent cohomology. -/
@[stacks 0FML] #check
  (AlgebraicGeometry.Scheme.RelativeFlatComplex.pushforward_mem_derivedQuasiCoherent
    a F K termIso hFlat hBoundedAbove hBoundedBelow :
      Scheme.derivedQuasiCoherentModuleProperty S
        ((RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)))

section LocalTor

variable [∀ U : TopologicalSpace.Opens S.toRingedSpace.carrier,
  DerivedCategory.DerivedTensor.Right.Has
    (C := RingedSpace.Modules (S.toRingedSpace.restrict U.isOpenEmbedding))]

/- Lemma 36.23.2 (3): the derived pushforward locally has finite Tor dimension. -/
@[stacks 0FML] #check
  (AlgebraicGeometry.Scheme.RelativeFlatComplex.pushforward_locallyHasFiniteTorDimension
    a F K termIso hFlat hBoundedAbove hBoundedBelow :
      LocallyHasFiniteTorDimension
        ((RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap a.toShHom)).obj (DerivedCategory.Q.obj K)))

end LocalTor

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
  [RingedSite.Hom.DerivedAdjunction.HasPair
    (RingedSpace.opensRingedSiteHom (ModuleCech.relativeSpaceMap a.toShHom))]
  [Functor.Monoidal
    (RingedSpace.modulePullbackDerived (ModuleCech.relativeSpaceMap a.toShHom))]

/- Lemma 36.23.2 (4): for a quasicoherent module, the canonical module projection-formula
map to the derived pushforward of the ordinary tensor complex is invertible. -/
@[stacks 0FML] #check
  (AlgebraicGeometry.Scheme.RelativeFlatComplex.moduleProjectionFormula
    a F K termIso hFlat hBoundedAbove hBoundedBelow :
      ∀ [Tensor.Has (ModuleCech.relativeSpace a.toShHom)]
        (tensorComparison :
          Tensor.functor (ModuleCech.relativeSpace a.toShHom) ≅
            MonoidalCategory.tensor
              (RingedSpace.ModuleDerived (ModuleCech.relativeSpace a.toShHom)))
        (G : Scheme.QCoh S),
        IsIso
          (moduleProjectionFormulaMap a tensorComparison K G))

/- Lemma 36.23.2 (5): the canonical derived projection-formula map is invertible for every
complex with quasicoherent cohomology on the base. -/
@[stacks 0FML] #check
  (AlgebraicGeometry.Scheme.RelativeFlatComplex.projectionFormula
    a F K termIso hFlat hBoundedAbove hBoundedBelow :
      ∀ L : Scheme.DerivedQCoh S,
        IsIso
          (ProjectionFormula.mate
            (ModuleCech.relativeSpaceMap a.toShHom) L.obj (DerivedCategory.Q.obj K)))

end ProjectionFormula

end AlgebraicGeometry.Scheme.RelativeFlatComplex
