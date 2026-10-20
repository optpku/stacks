/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle

@[expose] public section

/-!
# The vector-bundle locus of a perfect derived module

The degreewise fiber-Betti pattern defines the canonical open on which a perfect derived
module is a finite locally free module of fixed rank placed in one degree.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect

variable {X : Scheme.{u}} {E : RingedSpace.ModuleDerived X.toRingedSpace}

/-- For a perfect derived module, the locus with fiber Betti number `r` in degree `i` and
vanishing fiber Betti numbers in every other degree is open. -/
theorem isOpen_vectorBundleLocus (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ) :
    IsOpen {x : X | (fiberBetti E i x : ℤ) = r ∧
      ∀ j : ℤ, j ≠ i → fiberBetti E j x = 0} := sorry

/-- The canonical open on which a perfect derived module is a vector bundle of rank `r`
placed in degree `i`. -/
def vectorBundleLocus (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ) : X.Opens :=
  ⟨{x : X | (fiberBetti E i x : ℤ) = r ∧
      ∀ j : ℤ, j ≠ i → fiberBetti E j x = 0},
    isOpen_vectorBundleLocus hE i r⟩

/-- Membership in `vectorBundleLocus` is the prescribed degreewise fiber-Betti pattern. -/
theorem mem_vectorBundleLocus_iff
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ) (x : X) :
    x ∈ vectorBundleLocus hE i r ↔
      (fiberBetti E i x : ℤ) = r ∧
        ∀ j : ℤ, j ≠ i → fiberBetti E j x = 0 := sorry

/-- Formation of `vectorBundleLocus` commutes with arbitrary scheme pullback. -/
theorem vectorBundleLocus_pullback
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ)
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    f ⁻¹ᵁ vectorBundleLocus hE i r =
      vectorBundleLocus (RingedSpace.modulePullbackDerived_isPerfect f.toShHom E hE) i r := sorry

/-- The canonical vector-bundle locus carries the prescribed single-degree vector bundle,
and a morphism factors through it exactly when the derived pullback has that property. -/
theorem vectorBundleLocus_spec
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ) :
    IsVectorBundleOfRankInDegree
        ((RingedSpace.modulePullbackDerived (vectorBundleLocus hE i r).ι.toShHom).obj E) i r ∧
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X),
        (∃ g : Y ⟶ (vectorBundleLocus hE i r).toScheme,
          g ≫ (vectorBundleLocus hE i r).ι = f) ↔
        IsVectorBundleOfRankInDegree
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E) i r := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect
