/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On a regular Noetherian scheme of dimension `d`, every degree-`n` extension
class between coherent modules is zero when `d < n`. -/
@[stacks 0FZ3]
theorem ext_eq_zero_of_gt_dimension
    {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (n : ℕ) (hn : d < n)
    (e : @CategoryTheory.Abelian.Ext X.Modules inferInstance inferInstance
      (@CategoryTheory.IsGrothendieckAbelian.hasExt X.Modules inferInstance inferInstance
        (SheafOfModules.isGrothendieckAbelian X.ringCatSheaf)) F G n) :
    e = 0 := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- On a regular Noetherian scheme of dimension `d`, every morphism between
bounded coherent complexes is zero under a cohomological gap of width `d`. -/
@[stacks 0FZ3]
theorem hom_eq_zero_of_cohomology_gap
    {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (K L : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
    (a : ℤ)
    (hK : ∀ i : ℤ, i < a + (d : ℤ) →
      IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj K.obj))
    (hL : ∀ i : ℤ, a ≤ i →
      IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj L.obj))
    (f : K ⟶ L) :
    f = 0 := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
