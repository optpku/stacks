/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The `δ`-dimension of an irreducible closed subset, computed using its generic point and
the relative dimension function induced by `f`. -/
noncomputable def deltaDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : TopologicalSpace.IrreducibleCloseds X) : ℤ :=
  f.relativeDimensionFunction δ Z.isIrreducible.genericPoint

/-- The `δ`-dimension of an irreducible closed subset can be evaluated at any of its generic
points. -/
theorem deltaDimension_eq_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : TopologicalSpace.IrreducibleCloseds X) (ξ : X) (hξ : IsGenericPoint ξ Z) :
    f.deltaDimension δ Z = f.relativeDimensionFunction δ ξ := sorry

/-- The `δ`-dimension of a closed subscheme is the extended-integer supremum of the relative
dimension function at its generic points. -/
noncomputable def closedSubschemeDeltaDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) : EInt :=
  ⨆ η : genericPoints Z.subscheme,
    (f.relativeDimensionFunction δ (Z.subschemeι η.1) : EInt)

/-- The defining generic-point supremum formula for the `δ`-dimension of a closed subscheme. -/
theorem closedSubschemeDeltaDimension_def
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) :
    f.closedSubschemeDeltaDimension δ Z =
      ⨆ η : genericPoints Z.subscheme,
        (f.relativeDimensionFunction δ (Z.subschemeι η.1) : EInt) := sorry

/-- The `δ`-dimension of a closed subscheme as the supremum over its irreducible components. -/
theorem closedSubschemeDeltaDimension_eq_iSup_irreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) :
    f.closedSubschemeDeltaDimension δ Z =
      ⨆ C : irreducibleComponents Z.subscheme,
        (f.relativeDimensionFunction δ
          (Z.subschemeι (genericPoints.ofComponent C).1) : EInt) := sorry

end AlgebraicGeometry.Scheme.Hom
