/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Cycles and Chow classes with specified closed support

This file defines cycle and Chow groups carried by the reduced closed subscheme associated to a
closed subset, together with restriction and ambient pushforward maps.
-/

@[expose] public section

open CategoryTheory Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CycleGroup

/-- The degree-`k` cycle group carried by the reduced closed subscheme associated to `T`. -/
noncomputable abbrev onClosed {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :=
  CycleGroup (Scheme.IdealSheafData.vanishingIdeal T).subscheme
    (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ) k

/-- Push a cycle carried by a reduced closed subscheme to the ambient scheme. -/
noncomputable def onClosedPushforward {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    onClosed p δ T k →+ CycleGroup X (p.relativeDimensionFunction δ) k :=
  CycleGroup.mapHom (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
    (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
    (p.relativeDimensionFunction δ) k

/-- Restricting the coefficient function of an ambient cycle to a reduced closed subscheme
preserves local finiteness. -/
theorem restrictToClosed_locallyFiniteSupport {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    LocallyFiniteSupport fun z : (Scheme.IdealSheafData.vanishingIdeal T).subscheme ↦
      CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k α
        ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι z) := sorry

/-- The algebraic cycle obtained by restricting ambient coefficients to the reduced closed
subscheme associated to `T`. -/
noncomputable def restrictToClosedAlgebraicCycle {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    AlgebraicCycle (Scheme.IdealSheafData.vanishingIdeal T).subscheme ℤ where
  toFun := fun z ↦ CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k α
    ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι z)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun z _ ↦
    restrictToClosed_locallyFiniteSupport p δ T k α z

/-- Restriction of a degree-`k` ambient cycle to a reduced closed subscheme remains in degree
`k`. -/
theorem restrictToClosed_mem_dimensionSubgroup {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    restrictToClosedAlgebraicCycle p δ T k α ∈
      AlgebraicCycle.dimensionSubgroup
        (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
        k := sorry

/-- Restrict an ambient cycle to the reduced closed subscheme associated to `T`. -/
noncomputable def restrictToClosed {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) : onClosed p δ T k :=
  ⟨restrictToClosedAlgebraicCycle p δ T k α,
    restrictToClosed_mem_dimensionSubgroup p δ T k α⟩

/-- Restriction of ambient cycles to a reduced closed subscheme sends zero to zero. -/
theorem restrictToClosed_zero {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    restrictToClosed p δ T k 0 = 0 := sorry

/-- Restriction of ambient cycles to a reduced closed subscheme preserves addition. -/
theorem restrictToClosed_add {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k) :
    restrictToClosed p δ T k (α + β) =
      restrictToClosed p δ T k α + restrictToClosed p δ T k β := sorry

/-- The additive restriction map from ambient cycles to cycles on a reduced closed
subscheme. -/
noncomputable def restrictToClosedHom {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k →+ onClosed p δ T k where
  toFun := restrictToClosed p δ T k
  map_zero' := restrictToClosed_zero p δ T k
  map_add' := restrictToClosed_add p δ T k

end CycleGroup

namespace ChowGroup

/-- The degree-`k` Chow group carried by the reduced closed subscheme associated to `T`. -/
noncomputable abbrev onClosed {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :=
  @ChowGroup (Scheme.IdealSheafData.vanishingIdeal T).subscheme
    (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
      (LocallyOfFiniteType.isLocallyNoetherian p)
      (Scheme.IdealSheafData.vanishingIdeal T))
    (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
    inferInstance k

/-- Proper pushforward from the Chow group carried by `T` to the ambient Chow group. -/
noncomputable def onClosedPushforward {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    onClosed p δ T k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  map δ (Over.mk ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p))
    (Over.mk p) (Over.homMk (Scheme.IdealSheafData.vanishingIdeal T).subschemeι) k

/-- Supported Chow pushforward is the ordinary proper pushforward from the reduced closed
subscheme associated to `T`. -/
theorem onClosedPushforward_apply {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) (α : onClosed p δ T k) :
    onClosedPushforward p δ T k α =
      map δ (Over.mk ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p))
        (Over.mk p) (Over.homMk (Scheme.IdealSheafData.vanishingIdeal T).subschemeι) k α := sorry

/-- A Chow class together with a specified closed support whose reduced closed subscheme carries
the class. Its ambient Chow class is obtained by proper pushforward. -/
structure Supported {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) where
  /-- The specified closed support. -/
  support : TopologicalSpace.Closeds X
  /-- The Chow class on the reduced closed subscheme associated to the support. -/
  class_ : onClosed p δ support k

namespace Supported

/-- Construct a supported Chow class from a closed support and a class on its reduced closed
subscheme. -/
noncomputable def ofClosed {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) (class_ : onClosed p δ T k) :
    Supported p δ k where
  support := T
  class_ := class_

/-- The supported class constructor records exactly its supplied support and class. -/
theorem ofClosed_spec {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) (class_ : onClosed p δ T k) :
    (ofClosed p δ T k class_).support = T ∧
      (ofClosed p δ T k class_).class_ = class_ := sorry

/-- The ambient Chow class represented by a supported Chow class. -/
noncomputable def toAmbient {S X : Scheme.{u}} {p : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    {δ : S → ℤ} [IsDimensionFunction δ] {k : ℤ}
    (α : Supported p δ k) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k :=
  onClosedPushforward p δ α.support k α.class_

/-- The ambient view of a class supported on `T` is its proper pushforward from the reduced
closed subscheme associated to `T`. -/
theorem toAmbient_ofClosed {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (T : TopologicalSpace.Closeds X) (k : ℤ) (class_ : onClosed p δ T k) :
    toAmbient (ofClosed p δ T k class_) = onClosedPushforward p δ T k class_ := sorry

end Supported

end ChowGroup

end AlgebraicGeometry
