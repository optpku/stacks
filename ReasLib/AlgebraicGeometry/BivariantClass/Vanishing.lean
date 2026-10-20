module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification

/-!
# Vanishing criteria for bivariant classes

This file characterizes pointwise vanishing of a bivariant class by its action on
fundamental classes, including after proper birational modifications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- A bivariant class vanishes when each of its cap homomorphisms is zero. -/
def Vanishes
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass delta f p) : Prop :=
  ∀ {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ),
      c.cap i f' g square k = 0

/-- The pullback projections of a test scheme give compatible structure maps to the base. -/
theorem pullback_fst_comp_testScheme
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (V : Over Y.left) :
    pullback.fst V.hom f.left ≫ V.hom ≫ Y.hom =
      pullback.snd V.hom f.left ≫ X.hom := sorry

/-- A test scheme over the target determines a morphism of schemes over the base. -/
def testSchemeMorphism {S : Scheme.{u}} {Y : Over S} (V : Over Y.left) :
    Over.mk (V.hom ≫ Y.hom) ⟶ Y :=
  Over.homMk V.hom

/-- The underlying scheme morphism of `testSchemeMorphism V` is `V.hom`. -/
theorem testSchemeMorphism_left {S : Scheme.{u}} {Y : Over S} (V : Over Y.left) :
    (testSchemeMorphism V).left = V.hom := sorry

/-- Evaluate a bivariant class on the fundamental class of an integral test scheme. -/
noncomputable def capFundamentalClass
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
    (Over.homMk (pullback.fst V.hom f.left) (pullback_fst_comp_testScheme f V) :
      Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ Over.mk (V.hom ≫ Y.hom))
    (testSchemeMorphism V) (inferInstance : LocallyOfFiniteType V.hom)
    (IsPullback.of_hasPullback V.hom f.left).flip
    ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
    (@chowClass V.left (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
      ((V.hom ≫ Y.hom).relativeDimensionFunction delta) inferInstance
      ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
      (@CycleGroup.fundamental V.left
        (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
        ((V.hom ≫ Y.hom).relativeDimensionFunction delta)
        ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))))

/-- Fundamental-class evaluation is the cap map on the canonical pullback square. -/
theorem capFundamentalClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (c : BivariantClass delta f p) :
    capFundamentalClass delta X Y f p V c =
      @c.cap
        (Over.mk (pullback.snd V.hom f.left ≫ X.hom)) (Over.mk (V.hom ≫ Y.hom))
        (locallyOfFiniteType_comp (pullback.snd V.hom f.left) X.hom)
        (locallyOfFiniteType_comp V.hom Y.hom)
        (Over.homMk (pullback.snd V.hom f.left) :
          Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ X)
        (Over.homMk (pullback.fst V.hom f.left) (pullback_fst_comp_testScheme f V) :
          Over.mk (pullback.snd V.hom f.left ≫ X.hom) ⟶ Over.mk (V.hom ≫ Y.hom))
        (testSchemeMorphism V) (inferInstance : LocallyOfFiniteType V.hom)
        (IsPullback.of_hasPullback V.hom f.left).flip
        ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
        (@chowClass V.left (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
          ((V.hom ≫ Y.hom).relativeDimensionFunction delta) inferInstance
          ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left))
          (@CycleGroup.fundamental V.left
            (LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ Y.hom))
            ((V.hom ≫ Y.hom).relativeDimensionFunction delta)
            ((V.hom ≫ Y.hom).relativeDimensionFunction delta (genericPoint V.left)))) := sorry

/-- A class vanishes on integral fundamental classes when every such evaluation is zero. -/
def VanishesOnIntegralFundamentalClasses
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) : Prop :=
  ∀ (V : Over Y.left) [LocallyOfFiniteType V.hom] [IsIntegral V.left],
    capFundamentalClass delta X Y f p V c = 0

/-- Evaluate a bivariant class on an integral fundamental class after a modification. -/
noncomputable def capFundamentalClassAfterModification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (V' : Over V.left) (hmod : IsModification V'.hom)
    (c : BivariantClass delta f p) :=
  @capFundamentalClass S _ delta _ X Y _ _ f p ((Over.map V.hom).obj V')
    (@locallyOfFiniteType_comp _ _ _ V'.hom V.hom
      hmod.toIsProper.toLocallyOfFiniteType inferInstance)
    hmod.isIntegralSource c

/-- Evaluation after a modification is evaluation on the composite test scheme. -/
theorem capFundamentalClassAfterModification_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (V' : Over V.left) (hmod : IsModification V'.hom)
    (c : BivariantClass delta f p) :
    capFundamentalClassAfterModification delta X Y f p V V' hmod c =
      @capFundamentalClass S _ delta _ X Y _ _ f p ((Over.map V.hom).obj V')
        (@locallyOfFiniteType_comp _ _ _ V'.hom V.hom
          hmod.toIsProper.toLocallyOfFiniteType inferInstance)
        hmod.isIntegralSource c := sorry

/-- Vanishing after a modification descends to the original integral fundamental class. -/
theorem capFundamentalClass_eq_zero_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (V : Over Y.left)
    [LocallyOfFiniteType V.hom] [IsIntegral V.left]
    (V' : Over V.left) (hmod : IsModification V'.hom)
    (c : BivariantClass delta f p)
    (hvanish : capFundamentalClassAfterModification delta X Y f p V V' hmod c = 0) :
    capFundamentalClass delta X Y f p V c = 0 := sorry

/-- A class vanishes after modifications when each integral test scheme admits a
modification on whose fundamental class the evaluation is zero. -/
def VanishesAfterModification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) : Prop :=
  ∀ (V : Over Y.left) [LocallyOfFiniteType V.hom] [IsIntegral V.left],
    ∃ (V' : Over V.left) (hmod : IsModification V'.hom),
      capFundamentalClassAfterModification delta X Y f p V V' hmod c = 0

/-- A bivariant class vanishes exactly when it vanishes on every integral fundamental
class. -/
theorem vanishes_iff_integralFundamentalClasses
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    Vanishes delta c ↔ VanishesOnIntegralFundamentalClasses delta X Y f p c := sorry

/-- Vanishing on every integral fundamental class is equivalent to vanishing after a
modification of each integral test scheme. -/
theorem integralFundamentalClasses_iff_afterModification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    VanishesOnIntegralFundamentalClasses delta X Y f p c ↔
      VanishesAfterModification delta X Y f p c := sorry

/-- Pointwise vanishing, vanishing on integral fundamental classes, and vanishing after
modifications are equivalent conditions for a bivariant class. -/
theorem vanishingEquivalences
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    (Vanishes delta c ↔ VanishesOnIntegralFundamentalClasses delta X Y f p c) ∧
      (VanishesOnIntegralFundamentalClasses delta X Y f p c ↔
        VanishesAfterModification delta X Y f p c) := sorry

end AlgebraicGeometry.BivariantClass
