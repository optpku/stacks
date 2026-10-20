module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ZeroCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum

/-!
# Component decompositions of zero-section cycles
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The coefficient of the pushforward to `Y` of the zero cycle cut out on an irreducible
component. -/
noncomputable def componentZeroCycleCoeff {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) (y : Points Y) : ℤ :=
  let i := PointClosure.ι η.1
  ∑ᶠ z : Points (PointClosure.space η.1),
    @dite ℤ (Points.map i z = y) (Classical.propDecidable _)
      (fun _ ↦ zeroCycle (d ∘ Points.map i) ((pullback i).obj ℒ)
        (sectionsPullback i ℒ s) k z)
      (fun _ ↦ 0)

/-- The component zero-cycle coefficients have locally finite support. -/
theorem componentZeroCycleCoeff_locallyFiniteSupport {S : Scheme.{u}}
    {Y : AlgebraicSpace S} [IsLocallyNoetherian Y] (d : Points Y → ℤ)
    (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) (k : ℤ)
    (η : genericPoints Y) :
    LocallyFiniteSupport (componentZeroCycleCoeff d ℒ s k η) :=
  sorry

/-- The zero cycle cut out on an irreducible component, pushed forward to the ambient
space. -/
noncomputable def componentZeroCycle {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun := componentZeroCycleCoeff d ℒ s k η
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun y _ ↦
    componentZeroCycleCoeff_locallyFiniteSupport d ℒ s k η y

/-- The component zero cycle is the closed-immersion pushforward of the zero cycle of the
restricted section. -/
theorem componentZeroCycle_def {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) :
    (componentZeroCycle d ℒ s k η : Points Y → ℤ) =
      componentZeroCycleCoeff d ℒ s k η :=
  rfl

/-- The multiplicity-weighted component zero cycles of degree `k + 1` form a locally
finite family. -/
theorem componentZeroCyclesLocallyFinite {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    LocallyFinite fun η : genericPoints Y ↦
      (if d η.1 = k + 1 then
        (genericMultiplicity η : ℤ) • componentZeroCycle d ℒ s k η
      else 0).support :=
  sorry

/-- The locally finite, multiplicity-weighted sum of the zero cycles cut out on the
`(k + 1)`-dimensional irreducible components. -/
noncomputable def zeroCycleComponentSum {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun η : genericPoints Y ↦
      if d η.1 = k + 1 then
        (genericMultiplicity η : ℤ) • componentZeroCycle d ℒ s k η
      else 0)
    (componentZeroCyclesLocallyFinite d ℒ s k)

/-- Evaluation of the component sum is the pointwise finite sum of its weighted component
cycles. -/
theorem zeroCycleComponentSum_apply {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Points Y) :
    zeroCycleComponentSum d ℒ s k y = ∑ᶠ η : genericPoints Y,
      if d η.1 = k + 1 then
        (genericMultiplicity η : ℤ) * componentZeroCycle d ℒ s k η y
      else 0 :=
  sorry

/-- The component sum measured by the relative dimension function induced by `p` and
`δ`. -/
noncomputable def relativeZeroCycleComponentSum {S : Scheme.{u}}
    {B Y : AlgebraicSpace S} [UniversallyCatenary B] (p : Y ⟶ B)
    [QuasiSeparated p] [LocallyOfFiniteType p] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ :=
  @zeroCycleComponentSum S Y (LocallyOfFiniteType.isLocallyNoetherian p)
    (Hom.relativeDimensionFunction p δ) ℒ _ s k

/-- The relative component sum is the core component sum for
`p.relativeDimensionFunction δ`. -/
theorem relativeZeroCycleComponentSum_def {S : Scheme.{u}}
    {B Y : AlgebraicSpace S} [UniversallyCatenary B] (p : Y ⟶ B)
    [QuasiSeparated p] [LocallyOfFiniteType p] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycleComponentSum p δ ℒ s k =
      @zeroCycleComponentSum S Y (LocallyOfFiniteType.isLocallyNoetherian p)
        (Hom.relativeDimensionFunction p δ) ℒ _ s k :=
  rfl

/-- For a quasi-separated locally finite-type algebraic space over a universally
catenary base with dimension function, the zero cycle of a regular section of an
invertible module equals the locally finite sum of the zero cycles of its
restrictions to reduced irreducible components of dimension `k + 1`, weighted by
their generic multiplicities, provided every point has dimension at most `k + 1`. -/
theorem relativeZeroCycle_eq_sum_components
    {S : Scheme.{u}} {B Y : AlgebraicSpace S} [UniversallyCatenary B]
    (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections)
    [IsRegularSection ℒ s] (k : ℤ)
    (hY : ∀ y : Points Y, AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction p δ y ≤ k + 1) :
    relativeZeroCycle p δ ℒ s k = relativeZeroCycleComponentSum p δ ℒ s k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
