/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap62.Lemma_62_5_10_Family

/-!
# Families of relative fibre cycles

This file names the group of families of `r`-cycles on scheme-theoretic fibres
in the `RelativeCycle` namespace, reusing the Chap. 62 fibre-cycle API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A family of `r`-cycles on the scheme-theoretic fibres of `f : X ⟶ S`. -/
abbrev Family {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) : Type u :=
  familyOfCyclesOnFibres f r

/-- Base change of a family of fibrewise `r`-cycles along `g : S' ⟶ S`. -/
noncomputable abbrev baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) :
    Family f r →+ Family (pullback.snd f g) r :=
  FamilyOfCyclesOnFibres.baseChange f g r

#check (AlgebraicGeometry.FamilyOfCyclesOnFibres.baseChange_apply :
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (α : Family f r) (s' : S'),
    baseChange f g r α s' =
      FamilyOfCyclesOnFibres.fiberBaseChange f g r s' (α (g s')))

end AlgebraicGeometry.RelativeCycle
