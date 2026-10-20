/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Ext of rational points of projective space

Global Ext groups of the structure sheaf of a closed rational point of projective
space are finite-dimensional, with dimensions given by binomial coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Global `Ext` of `z.pushforwardStructureModule` with itself, as a `k`-module induced
by `toSpec k n`, for a section `z` of the structure morphism. -/
noncomputable abbrev extValue {k : Type u} [Field k] {n : ℕ}
    (z : Spec (CommRingCat.of k) ⟶ scheme k n)
    (hz : z ≫ toSpec k n = 𝟙 _) (i : ℤ) : ModuleCat.{u + 1} k :=
  let OZ := (DerivedCategory.singleFunctor (scheme k n).Modules 0).obj
    z.pushforwardStructureModule
  DerivedExt.value (toSpec k n) OZ OZ i

/-- If `hz : z ≫ toSpec k n = 𝟙 _`, then `extValue z hz i` is finite-dimensional over `k`. -/
instance finiteDimensional_extValue {k : Type u} [Field k] {n : ℕ}
    (z : Spec (CommRingCat.of k) ⟶ scheme k n)
    (hz : z ≫ toSpec k n = 𝟙 _) (i : ℤ) :
    FiniteDimensional k (extValue z hz i) := sorry

/-- For a closed `k`-rational point of `scheme k n`, the dimension of its degree-`i`
self-Ext is `n.choose i.toNat` when `0 ≤ i` and zero when `i < 0`. -/
theorem finrank_extValue {k : Type u} [Field k] (n : ℕ)
    (z : Spec (CommRingCat.of k) ⟶ scheme k n)
    (hz : z ≫ toSpec k n = 𝟙 _) (i : ℤ) :
    Module.finrank k (extValue z hz i) =
      if 0 ≤ i then n.choose i.toNat else 0 := sorry

/-- The closed `k`-rational point `(1 : 0 : … : 0)` of `scheme k n`, obtained as the
origin of the standard `T_0`-chart. -/
noncomputable def standardRationalPoint (k : Type u) [Field k] (n : ℕ) :
    Spec (CommRingCat.of k) ⟶ scheme k n :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k)))
      (fun _ : ULift.{u} (Fin n) ↦ 0) ≫
    (CoordinateChart.iso n 0).inv ≫ (coordinateBasicOpen n 0).1.ι

/-- `standardRationalPoint k n` is a section of the structure morphism `toSpec k n`. -/
theorem standardRationalPoint_comp_toSpec (k : Type u) [Field k] (n : ℕ) :
    standardRationalPoint k n ≫ toSpec k n = 𝟙 _ := sorry

end AlgebraicGeometry.ProjectiveSpace
