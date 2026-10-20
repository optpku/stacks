/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of equidimensional relative cycles along flat pullbacks

Equidimensionality of a relative cycle can be checked after flat pullback along
a jointly surjective family of morphisms of fixed relative dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- A relative `r`-cycle over a locally Noetherian base with locally finite-type
structure morphism is equidimensional if and only if its flat pullbacks along a
jointly surjective family of flat morphisms of relative dimension `e` are
equidimensional. -/
@[stacks 0H5N]
theorem isEquidimensional_iff_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : f.FiberCycleFamily r) (hα : IsRelative α) :
    Equidimensional α ↔ ∀ i, Equidimensional (flatPullback (family i).hom e α) :=
  sorry

/-- If every flat pullback of a relative `r`-cycle along a jointly surjective
family of flat morphisms of relative dimension `e` is equidimensional, then
the relative cycle is equidimensional. -/
theorem isEquidimensional_of_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : f.FiberCycleFamily r) (hα : IsRelative α)
    (h : ∀ i, Equidimensional (flatPullback (family i).hom e α)) :
    Equidimensional α :=
  sorry

end AlgebraicGeometry.RelativeCycle
