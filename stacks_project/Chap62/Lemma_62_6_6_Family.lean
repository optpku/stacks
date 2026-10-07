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
abbrev Family {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Type u :=
  familyOfCyclesOnFibres f r

/-- Two fibrewise cycle families are equal if and only if they agree on every fibre. -/
theorem family_ext {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} {α β : Family f r} :
    α = β ↔ ∀ s : S, α s = β s := sorry

/-- Base change of a family of fibrewise `r`-cycles along `g : S' ⟶ S`. -/
noncomputable abbrev baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) :
    Family f r →+ Family (pullback.snd f g) r :=
  FamilyOfCyclesOnFibres.baseChange f g r

/-- Evaluating a base-changed family at `s'` is fibrewise field-extension pullback of the original
fibre cycle. -/
theorem baseChange_eval {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : Family f r) (s' : S') :
    baseChange f g r α s' =
      FamilyOfCyclesOnFibres.fiberBaseChange f g r s' (α (g s')) := sorry

end AlgebraicGeometry.RelativeCycle
