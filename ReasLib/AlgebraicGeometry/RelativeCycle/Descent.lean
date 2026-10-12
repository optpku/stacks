/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functoriality

/-!
# Flat descent of relative cycles

Relativity of fibre-cycle families is local for jointly surjective families
of flat, locally finite type morphisms of fixed relative dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- A fibre-cycle family over a locally Noetherian base is relative if and only if
its flat pullbacks along a jointly surjective family of locally finite type
morphisms of fixed relative dimension are relative. -/
theorem isRelative_iff_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : f.FiberCycleFamily r) :
    IsRelative α ↔ ∀ i, IsRelative (flatPullback (family i).hom e α) := sorry

/-- A fibre-cycle family over a locally Noetherian base is relative when all its
flat pullbacks along a jointly surjective family of locally finite type morphisms
of fixed relative dimension are relative. -/
theorem isRelative_of_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : f.FiberCycleFamily r)
    (h : ∀ i, IsRelative (flatPullback (family i).hom e α)) :
    IsRelative α := sorry

end AlgebraicGeometry.RelativeCycle
