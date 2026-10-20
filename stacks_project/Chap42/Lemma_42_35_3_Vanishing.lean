/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Remark_42_33_5_Bivariant
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ChowGroup

/-- The Chow class represented by the degree-`k` fundamental cycle. -/
noncomputable def fundamentalClass {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (d : Z → ℤ) [IsDimensionFunction d] (k : ℤ) : ChowGroup Z d k :=
  chowClass d k (CycleGroup.fundamental d k)

/-- The fundamental Chow class is the class of `CycleGroup.fundamental`. -/
theorem fundamentalClass_def {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (d : Z → ℤ) [IsDimensionFunction d] (k : ℤ) :
    fundamentalClass d k = chowClass d k (CycleGroup.fundamental d k) := sorry

end ChowGroup

namespace BivariantClass

/-- The cap family which is zero on every cartesian test square and Chow class. -/
def zeroCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : CapFamily delta f p :=
  fun {_ _} _ _ _ _ _ _ _ _ ↦ 0

/-- The zero cap family evaluates to zero. -/
theorem zeroCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (alpha : RelativeChow delta Y' k) :
    zeroCap delta f p i f' g square k alpha = 0 := sorry

/-- The pointwise-zero cap family respects proper pushforward. -/
theorem zeroCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :
    CompatibleWithProperPushforward delta (zeroCap delta f p) := sorry

/-- The pointwise-zero cap family respects flat pullback. -/
theorem zeroCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :
    CompatibleWithFlatPullback delta (zeroCap delta f p) := sorry

/-- The pointwise-zero cap family respects effective-Cartier Gysin pullback. -/
theorem zeroCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :
    CompatibleWithCartierGysin delta (zeroCap delta f p) := sorry

/-- The cap action of the zero bivariant class is the zero cap family. -/
theorem zeroClass_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :
    ((pointwiseZero delta f p).cap : CapFamily delta f p) =
      (zeroCap delta f p : CapFamily delta f p) := rfl

/-- Bivariant classes have the canonical pointwise-zero value. -/
instance instZeroBivariantClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : Zero (BivariantClass delta f p) where
  zero := pointwiseZero delta f p

/-- The two pullback projections define compatible structure maps to the base scheme. -/
theorem pullback_fst_over
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (V : Over Y.left) :
    pullback.fst V.hom f.left ≫ V.hom ≫ Y.hom =
      pullback.snd V.hom f.left ≫ X.hom := sorry

/-- The structure map of a test scheme over `Y` defines the corresponding morphism of
schemes over the base. -/
def testSchemeToTarget
    {S : Scheme.{u}} {Y : Over S} (V : Over Y.left) :
    Over.mk (V.hom ≫ Y.hom) ⟶ Y :=
  Over.homMk V.hom

/-- The underlying scheme morphism of `testSchemeToTarget` is the given structure map. -/
theorem testSchemeToTarget_left
    {S : Scheme.{u}} {Y : Over S} (V : Over Y.left) :
    (testSchemeToTarget V).left = V.hom := sorry

/-- Evaluate a bivariant class on the fundamental class of an integral test scheme. -/
noncomputable def capFundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (c : BivariantClass delta f p) :
    @RelativeChow S _ delta _ (Over.mk (pullback.snd V.hom f.left ≫ X.hom))
      (locallyOfFiniteType_comp (pullback.snd V.hom f.left) X.hom)
      ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left) - p) :=
  @c.cap
    (Over.mk (pullback.snd V.hom f.left ≫ X.hom)) (Over.mk (V.hom ≫ Y.hom))
    (locallyOfFiniteType_comp (pullback.snd V.hom f.left) X.hom)
    (locallyOfFiniteType_comp V.hom Y.hom)
    (Over.homMk (pullback.snd V.hom f.left) :
      Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ X)
    (Over.homMk (pullback.fst V.hom f.left) (pullback_fst_over f V) :
      Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ Over.mk (V.hom ≫ Y.hom))
    (testSchemeToTarget V)
    (inferInstance : LocallyOfFiniteType V.hom)
    (IsPullback.of_hasPullback V.hom f.left).flip
    ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
    (@ChowGroup.fundamentalClass V.left
      (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
      ((V.hom ≫ Y.hom).relativeDimensionFunction delta) inferInstance
      ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left)))

/-- `capFundamental` is the cap evaluation on the canonical pullback square and
fundamental Chow class. -/
theorem capFundamental_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (c : BivariantClass delta f p) :
    capFundamental delta X Y f p V c =
      @c.cap
        (Over.mk (pullback.snd V.hom f.left ≫ X.hom)) (Over.mk (V.hom ≫ Y.hom))
        (locallyOfFiniteType_comp (pullback.snd V.hom f.left) X.hom)
        (locallyOfFiniteType_comp V.hom Y.hom)
        (Over.homMk (pullback.snd V.hom f.left) :
          Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ X)
        (Over.homMk (pullback.fst V.hom f.left) (pullback_fst_over f V) :
          Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ Over.mk (V.hom ≫ Y.hom))
        (testSchemeToTarget V)
        (inferInstance : LocallyOfFiniteType V.hom)
        (IsPullback.of_hasPullback V.hom f.left).flip
        ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
        (@ChowGroup.fundamentalClass V.left
          (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
          ((V.hom ≫ Y.hom).relativeDimensionFunction delta) inferInstance
          ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))) := sorry

/-- Evaluate a bivariant class on the fundamental class after an explicit modification. -/
noncomputable def capFundamentalModification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (V' : Over V.left) (hmod : IsModification V'.hom)
    (c : BivariantClass delta f p) :=
  @capFundamental S _ delta _ X Y _ _ f p ((Over.map V.hom).obj V')
    (@locallyOfFiniteType_comp _ _ _ V'.hom V.hom
      hmod.toIsProper.toLocallyOfFiniteType inferInstance)
    hmod.isIntegralSource c

/-- Evaluation after a modification is `capFundamental` for the composite test scheme. -/
theorem capFundamentalModification_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (V' : Over V.left) (hmod : IsModification V'.hom)
    (c : BivariantClass delta f p) :
    capFundamentalModification delta X Y f p V V' hmod c =
      @capFundamental S _ delta _ X Y _ _ f p ((Over.map V.hom).obj V')
        (@locallyOfFiniteType_comp _ _ _ V'.hom V.hom
          hmod.toIsProper.toLocallyOfFiniteType inferInstance)
        hmod.isIntegralSource c := sorry

end BivariantClass

end AlgebraicGeometry
