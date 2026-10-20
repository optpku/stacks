/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.RelativeCycle.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Equidimensional relative cycles

Equidimensionality bounds the relative dimension of a closed subscheme containing
the support of a family of fibre cycles. Restriction, base change, and flat
pullback preserve this condition for relative cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- A family of `r`-cycles on fibres is equidimensional when its support is
contained in a closed subscheme of relative dimension at most `r`. -/
def Equidimensional {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : CyclesOnFibers f r) : Prop :=
  ∃ W : X.IdealSheafData,
    support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r

/-- Equidimensionality means there is a closed subscheme containing the support
and of relative dimension at most `r`. -/
theorem equidimensional_iff {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : CyclesOnFibers f r) :
    Equidimensional α ↔
      ∃ W : X.IdealSheafData,
        support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)

/-- The zero family of fibrewise `r`-cycles is equidimensional. -/
theorem isEquidimensional_zero : Equidimensional (0 : f.FiberCycleFamily r) := sorry

/-- The sum of equidimensional families of fibrewise `r`-cycles on a locally
finite-type morphism is equidimensional. -/
theorem isEquidimensional_add {α β : f.FiberCycleFamily r}
    (hα : Equidimensional α) (hβ : Equidimensional β) :
    Equidimensional (α + β) := sorry

/-- The negative of an equidimensional family of fibrewise `r`-cycles is
equidimensional. -/
theorem isEquidimensional_neg {α : f.FiberCycleFamily r} (hα : Equidimensional α) :
    Equidimensional (-α) := sorry

variable [IsLocallyNoetherian S]

/-- The abelian group `z_equi(X/S, r)` of equidimensional relative `r`-cycles on
`X / S`: the relative `r`-cycles whose support is contained in a closed
subscheme of relative dimension at most `r`. -/
def equidimensional : AddSubgroup (f.FiberCycleFamily r) where
  carrier := {α | IsRelative α ∧ Equidimensional α}
  zero_mem' := ⟨isRelative_zero f r, isEquidimensional_zero f r⟩
  add_mem' ha hb := ⟨isRelative_add f r ha.1 hb.1, isEquidimensional_add f r ha.2 hb.2⟩
  neg_mem' ha := ⟨isRelative_neg f r ha.1, isEquidimensional_neg f r ha.2⟩

/-- Membership in `z_equi(X/S, r)` is the conjunction of the relative-cycle
condition and equidimensionality of the family of fibre cycles. -/
theorem mem_equidimensional (α : f.FiberCycleFamily r) :
    α ∈ equidimensional f r ↔ IsRelative α ∧ Equidimensional α :=
  sorry

/-- A family lies in `z_equi(X/S, r)` if and only if it is a relative `r`-cycle
and its support is contained in a closed subscheme of relative dimension at
most `r`. -/
theorem mem_equidimensional_iff_support (α : f.FiberCycleFamily r) :
    α ∈ equidimensional f r ↔
      IsRelative α ∧
        ∃ W : X.IdealSheafData,
          support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r :=
  sorry

end AlgebraicGeometry.RelativeCycle

namespace AlgebraicGeometry

open RelativeCycle

/-- Restriction to compatible opens preserves equidimensionality of relative
`r`-cycles over a locally Noetherian base with locally finite-type structure
morphism. -/
theorem equidimensional_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r}
    (h_rel : IsRelative α) (h_eq : Equidimensional α) (U : X.Opens) (V : S.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    Equidimensional (FiberCycleFamily.restrict U V hUV α) := sorry

/-- Arbitrary base change preserves equidimensionality of relative `r`-cycles
over a locally Noetherian base with locally finite-type structure morphism. -/
theorem equidimensional_baseChange {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℕ}
    {α : f.FiberCycleFamily r} (h_rel : IsRelative α) (h_eq : Equidimensional α) :
    Equidimensional (FamilyOfCyclesOnFibres.baseChange f g r α) := sorry

/-- Flat pullback along a morphism of relative dimension `e` preserves
equidimensionality of relative `r`-cycles over a locally Noetherian base with
locally finite-type structure morphism, yielding cycles of degree `r + e`. -/
theorem equidimensional_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (h : X' ⟶ X) (e : ℕ)
    [Flat h] [RelativeDimension h e] {r : ℕ} {α : f.FiberCycleFamily r}
    (h_rel : IsRelative α) (h_eq : Equidimensional α) :
    Equidimensional (RelativeCycle.flatPullback h e α) := sorry

end AlgebraicGeometry
