module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap62.«62_6_8_1_CycleClass»

/-!
# Lemma 62.6.10

Surjectivity of the Hilbert cycle-class homomorphism over a discrete valuation
ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.10: if `f : X ⟶ S` is of finite type and `S` is the spectrum of a
discrete valuation ring, then for every `r ≥ 0` the Hilbert cycle-class
homomorphism `cycleClassHomToGroup` (62.6.8.1) from `FreeAbelianGroup (Hilb f r)`
to `group f r` is surjective. -/
@[stacks 0H5A]
theorem cycleClassHomToGroup_surjective
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ) :
    Function.Surjective (cycleClassHomToGroup f r) :=
  sorry

/-- Every relative `r`-cycle on `X / Spec R` lies in the image of
`cycleClassHom`. -/
theorem mem_range_cycleClassHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ)
    {α : Family f r} (hα : IsRelative α) :
    α ∈ Set.range (cycleClassHom f r) :=
  sorry

end AlgebraicGeometry.RelativeCycle
