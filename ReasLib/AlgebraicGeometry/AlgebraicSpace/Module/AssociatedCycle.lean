/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic

/-!
# Associated cycles of coherent modules

Component multiplicities are finite lengths at generic points of coherent support.
Associated cycles retain the multiplicity coefficients in a prescribed dimension.
For a good morphism, the support-dimension bound specifies the associated cycle's degree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The multiplicity of an irreducible component of `moduleSupport F` is the length of
`F` at the generic point of that component. -/
noncomputable def componentMultiplicity [IsLocallyNoetherian X] [IsDecent X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) : ℕ :=
  (lengthAt F x).toNat

/-- The component multiplicity is the finite value of `lengthAt` at the generic point. -/
theorem componentMultiplicity_eq_lengthAt [IsLocallyNoetherian X] [IsDecent X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    (componentMultiplicity F x hx : ℕ∞) = lengthAt F x :=
  sorry

/-- The component multiplicity witnesses `hasLengthAt` at the generic point. -/
theorem hasLengthAt_componentMultiplicity [IsLocallyNoetherian X] [IsDecent X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    hasLengthAt F x (componentMultiplicity F x hx) :=
  sorry

/-- The multiplicity of an irreducible component of the support of a coherent module is a
positive integer. -/
theorem componentMultiplicity_pos [IsLocallyNoetherian X] [IsDecent X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    0 < componentMultiplicity F x hx :=
  sorry

open Classical in
/-- The multiplicity-weighted coefficient function of a coherent module, restricted to its
dimension-`k` support generic points, has locally finite support. -/
theorem associatedCycle_locallyFiniteSupport [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      if IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k then
        ((lengthAt F x).toNat : ℤ) else 0 :=
  sorry

open Classical in
/-- The multiplicity-weighted degree-`k` cycle associated to a coherent `𝒪_X`-module. -/
noncomputable def associatedCycle [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    if IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k then
      ((lengthAt F x).toNat : ℤ) else 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    associatedCycle_locallyFiniteSupport F d k x

open Classical in
/-- Coefficients of the associated cycle are the length at a dimension-`k` generic point of
the support, and vanish otherwise. -/
theorem associatedCycle_apply [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) (x : Points X) :
    associatedCycle F d k x =
      if IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k then
        ((lengthAt F x).toNat : ℤ) else 0 :=
  rfl

/-- Off the dimension-`k` locus, the associated cycle coefficient vanishes. -/
theorem associatedCycle_eq_zero_of_dimension_ne [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) {x : Points X}
    (hx : d x ≠ k) : associatedCycle F d k x = 0 :=
  sorry

end Modules

namespace Hom

/-- The `δ`-dimension of the support of a coherent `𝒪_X`-module. -/
noncomputable def moduleSupportDeltaDimension {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] : EInt :=
  (closedSetDeltaDimension f) δ
    ⟨Modules.moduleSupport F,
      Modules.isClosed_moduleSupport F⟩

/-- The dimension of coherent support is its closed-set dimension. -/
theorem moduleSupportDeltaDimension_def {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] :
    (moduleSupportDeltaDimension f) δ F =
      (closedSetDeltaDimension f) δ
        ⟨Modules.moduleSupport F,
          Modules.isClosed_moduleSupport F⟩ :=
  rfl

/-- The degree-`k` cycle associated to a coherent `𝒪_X`-module, measured using the
relative dimension function of a good morphism. -/
noncomputable def moduleCycle {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Modules.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) F _
    ((relativeDimensionFunction f) δ) k

open Classical in
/-- Coefficients of the module cycle are the length at a `δ`-dimension-`k` generic point of
the support, and vanish otherwise. -/
theorem moduleCycle_apply {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) (x : Points X) :
    moduleCycle f δ F k hF x =
      if IsGenericPoint.ofIrreducibleComponent x (Modules.moduleSupport F) ∧
          (relativeDimensionFunction f) δ x = k then
        ((Modules.lengthAt F x).toNat : ℤ) else 0 :=
  rfl

/-- The cycle of a coherent module whose support has dimension at most `k` belongs to
the group of cycles supported in relative dimension `k`. -/
theorem moduleCycle_mem {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) :
    moduleCycle f δ F k hF ∈ cycleGroup f δ k :=
  sorry

/-- For a coherent module whose support has `δ`-dimension at most `k`, the coefficient
of an integral closed subspace of `δ`-dimension `k` in its associated cycle is the
length of the module at the generic point of that subspace. -/
@[stacks 0EEC]
theorem moduleCycle_eq_lengthAt
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
    (k : ℤ) (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt))
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : (closedSubspaceDeltaDimension f) δ Z = (k : EInt))
    (ξ : Points X) (hξ : IsGenericPoint ξ Z.pointsSet) :
    moduleCycle f δ F k hF ξ = (Modules.lengthAt F ξ).toNat :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
