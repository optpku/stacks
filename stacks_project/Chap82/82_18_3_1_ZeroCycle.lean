module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap82.Lemma_82_4_1_Length

/-!
# Zero cycles of sections on algebraic spaces

This file owns the relative dimension function along a morphism of algebraic spaces, the
integral component and generic multiplicity of a point of `|Y|`, and the `k`-cycle of the
zero scheme of a section of an invertible module, together with its multiplicity-weighted
component sum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The relative dimension function associated to `p : Y ⟶ B` and `δ : |B| → ℤ` sends a
point `y` to `δ (p(y))` plus the residue-field transcendence degree of `y` over `p(y)`. -/
noncomputable def relativeDimensionFunction {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (p : Y ⟶ B) (δ : Points B → ℤ) : Points Y → ℤ :=
  fun y ↦ δ (Points.map p y) + (residueFieldTrdegAt p y : ℤ)

/-- `p.relativeDimensionFunction δ` evaluates to `δ` at the image in `|B|` plus the
residue-field transcendence degree of `p` at `y`. -/
theorem relativeDimensionFunction_apply {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (p : Y ⟶ B) (δ : Points B → ℤ) (y : Points Y) :
    p.relativeDimensionFunction δ y =
      δ (Points.map p y) + (residueFieldTrdegAt p y : ℤ) :=
  sorry

/-- Along a good morphism to a universally catenary algebraic space, adding residue-field
transcendence degree to a dimension function on the target yields a dimension function. -/
instance instIsDimensionFunction_relativeDimensionFunction
    {S : Scheme.{u}} {B Y : AlgebraicSpace S} [UniversallyCatenary B]
    (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ] :
    IsDimensionFunction (p.relativeDimensionFunction δ) :=
  sorry

end Hom

/-- The integral closed subspace whose underlying point-set is the closure of a generic
point of `|Y|`. -/
noncomputable def integralComponent {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (η : genericPoints Y) : ClosedSubspace Y :=
  (ClosedSubspaceStructure.reduced (Closeds.closure {η.1})).subspace

/-- The inclusion of an integral component is the reduced induced structure on the closure
of the generic point. -/
theorem integralComponent_ι {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (η : genericPoints Y) :
    (integralComponent η).ι =
      (ClosedSubspaceStructure.reduced (Closeds.closure {η.1})).ι :=
  sorry

/-- The underlying point-set of an integral component is the closure of its generic
point. -/
theorem integralComponent_pointsSet_eq_closure {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (η : genericPoints Y) :
    (integralComponent η).pointsSet = closure {η.1} :=
  sorry

/-- An integral component of a locally Noetherian algebraic space is locally Noetherian. -/
instance instIsLocallyNoetherian_integralComponent {S : Scheme.{u}}
    {Y : AlgebraicSpace S} [IsLocallyNoetherian Y] (η : genericPoints Y) :
    IsLocallyNoetherian (integralComponent η).X :=
  instIsLocallyNoetherian_of_isClosedImmersion (integralComponent η)

/-- The multiplicity of a generic point is the finite étale-stalk length of `𝒪_Y` at any
geometric point over that generic point. -/
noncomputable def genericMultiplicity {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (η : genericPoints Y) : ℕ :=
  (⨆ p : {p : GeometricPoint Y // p.liesOver η.1},
      Modules.lengthAtGeometricPoint
        (SheafOfModules.unit (structureSheaf Y) : Y.Modules) p.1).toNat

/-- The generic-point multiplicity recovers the étale-stalk length of `𝒪_Y` at any
geometric point over the generic point. -/
theorem genericMultiplicity_eq_length {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (η : genericPoints Y)
    (xbar : GeometricPoint Y) (hx : xbar.liesOver η.1) :
    (genericMultiplicity η : ℕ∞) =
      Modules.lengthAtGeometricPoint
        (SheafOfModules.unit (structureSheaf Y) : Y.Modules) xbar :=
  sorry

namespace Modules

/-- Pullback of modules along a morphism of algebraic spaces preserves
tensor-invertibility. -/
instance instIsInvertibleObject_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ℒ : Y.Modules) [isInvertibleObject ℒ] :
    isInvertibleObject ((pullback f).obj ℒ) :=
  sorry

/-- The zero scheme of a section of an invertible module on a locally Noetherian algebraic
space is locally Noetherian. -/
instance instIsLocallyNoetherian_zeroScheme {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    IsLocallyNoetherian (zeroScheme ℒ s).X :=
  instIsLocallyNoetherian_of_isClosedImmersion (zeroScheme ℒ s)

/-- The coefficient of `[Z(s)]_k` at a point `y` of `|Y|`. -/
noncomputable def zeroCycleCoeff {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Points Y) : ℤ :=
  ∑ᶠ η : genericPoints (zeroScheme ℒ s).X,
    @dite ℤ (Points.map (zeroSchemeι ℒ s) η.1 = y ∧ d y = k)
      (Classical.propDecidable _)
      (fun _ ↦ (genericMultiplicity η : ℤ)) (fun _ ↦ 0)

/-- The coefficient function of `[Z(s)]_k` has locally finite support. -/
theorem zeroCycleCoeff_locallyFiniteSupport {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    LocallyFiniteSupport (zeroCycleCoeff d ℒ s k) :=
  sorry

/-- The degree-`k` cycle of the zero scheme of `s`, as a locally finite function on
`|Y|`. -/
noncomputable def zeroCycle {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ where
  toFun := zeroCycleCoeff d ℒ s k
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun y _ ↦
    zeroCycleCoeff_locallyFiniteSupport d ℒ s k y

/-- Evaluation of `[Z(s)]_k` recovers the associated coefficient function. -/
theorem zeroCycle_apply {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Points Y) :
    zeroCycle d ℒ s k y = zeroCycleCoeff d ℒ s k y :=
  sorry

/-- The zero cycle is the locally finite packaging of `zeroCycleCoeff`. -/
theorem zeroCycle_def {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    (zeroCycle d ℒ s k : Points Y → ℤ) = zeroCycleCoeff d ℒ s k :=
  sorry

/-- The coefficient of the pushforward to `Y` of the zero cycle cut out on an irreducible
component. -/
noncomputable def componentZeroCycleCoeff {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) (y : Points Y) : ℤ :=
  let i := (integralComponent η).ι
  ∑ᶠ z : Points (integralComponent η).X,
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
  sorry

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

/-- The zero-section cycle measured by the relative dimension function induced by `p` and
`δ`. -/
noncomputable def relativeZeroCycle {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ :=
  @zeroCycle S Y (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) ℒ _ s k

/-- The relative zero cycle is the core zero cycle for `p.relativeDimensionFunction δ`. -/
theorem relativeZeroCycle_def {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycle p δ ℒ s k =
      @zeroCycle S Y (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) ℒ _ s k :=
  sorry

/-- The component sum measured by the relative dimension function induced by `p` and
`δ`. -/
noncomputable def relativeZeroCycleComponentSum {S : Scheme.{u}}
    {B Y : AlgebraicSpace S} [UniversallyCatenary B] (p : Y ⟶ B)
    [QuasiSeparated p] [LocallyOfFiniteType p] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ :=
  @zeroCycleComponentSum S Y (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) ℒ _ s k

/-- The relative component sum is the core component sum for
`p.relativeDimensionFunction δ`. -/
theorem relativeZeroCycleComponentSum_def {S : Scheme.{u}}
    {B Y : AlgebraicSpace S} [UniversallyCatenary B] (p : Y ⟶ B)
    [QuasiSeparated p] [LocallyOfFiniteType p] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycleComponentSum p δ ℒ s k =
      @zeroCycleComponentSum S Y (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) ℒ _ s k :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
