module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_7_3_Equidimensional

/-!
# Equidimensional relative cycles

This file names the additive group `z_equi(X/S, r)` of equidimensional relative
`r`-cycles on a locally finite type morphism `f : X ⟶ S` from a locally
Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.CyclesOnFibers

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

#check (AlgebraicGeometry.RelativeCycle.isEquidimensional_zero :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ),
    Equidimensional (0 : f.FiberCycleFamily r))

#check (AlgebraicGeometry.RelativeCycle.isEquidimensional_add :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    {α β : f.FiberCycleFamily r},
    Equidimensional α → Equidimensional β → Equidimensional (α + β))

#check (AlgebraicGeometry.RelativeCycle.isEquidimensional_neg :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) {α : f.FiberCycleFamily r},
    Equidimensional α → Equidimensional (-α))

#check (AlgebraicGeometry.RelativeCycle.equidimensional :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) [IsLocallyNoetherian S], AddSubgroup (f.FiberCycleFamily r))

#check (AlgebraicGeometry.RelativeCycle.mem_equidimensional :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) [IsLocallyNoetherian S]
    (α : f.FiberCycleFamily r),
    α ∈ equidimensional f r ↔ IsRelative α ∧ Equidimensional α)

#check (AlgebraicGeometry.RelativeCycle.mem_equidimensional_iff_support :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) [IsLocallyNoetherian S]
    (α : f.FiberCycleFamily r),
    α ∈ equidimensional f r ↔
      IsRelative α ∧
        ∃ W : X.IdealSheafData,
          support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r)

end AlgebraicGeometry.RelativeCycle
