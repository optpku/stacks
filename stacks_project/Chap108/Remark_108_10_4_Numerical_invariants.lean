/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_5_6_Map
public import stacks_project.Chap108.Remark_108_10_4_Numerical_invariants_Locus
import StacksCheckRecall

/-!
# Remark 108.10.4 (Numerical invariants)

The numerical relative-Hom functor `Mor^P_B(Y, X)` is the intersection of
`Mor_B(Y, X)` with `Hilb^P_{Y ×_B X/B}`. The morphism
`Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is a flat closed immersion, and an open
immersion if `I` is finite, or `B` is locally Noetherian, or the family is
`n ↦ L^{⊗ n}` for invertible `L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/- Remark 108.10.4 (Numerical invariants) (1) -/
@[stacks 0DPQ] #check morNumerical

/-- Remark 108.10.4 (Numerical invariants) (2): the morphism
`morNumericalι : morNumerical ⟶ mor` is a closed immersion. -/
@[stacks 0DPQ]
theorem isClosedImmersion_morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsClosedImmersionOnSchemesOver (morNumericalι y x E P hE) :=
  sorry

/-- Remark 108.10.4 (Numerical invariants) (3): the morphism
`morNumericalι : morNumerical ⟶ mor` is flat. -/
@[stacks 0DPQ]
theorem isFlat_morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsFlatOnSchemesOver (morNumericalι y x E P hE) :=
  sorry

/-- Remark 108.10.4 (Numerical invariants) (4): if `I` is finite, then the
morphism `morNumericalι : morNumerical ⟶ mor` is an open immersion. -/
@[stacks 0DPQ]
theorem isOpenImmersion_morNumericalι_of_finite (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} [Finite I] (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE) :=
  sorry

/-- Remark 108.10.4 (Numerical invariants) (5): if `B` is locally Noetherian,
then the morphism `morNumericalι : morNumerical ⟶ mor` is an open immersion. -/
@[stacks 0DPQ]
theorem isOpenImmersion_morNumericalι_of_locallyNoetherian (y : Y ⟶ B)
    (x : X ⟶ B) [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE) :=
  sorry

/-- Remark 108.10.4 (Numerical invariants) (6): if `E n = L^{⊗ n}` for an
invertible `𝒪_{Y ×_B X}`-module `L`, then the morphism
`morNumericalHilbert ⟶ mor` is an open immersion. -/
@[stacks 0DPQ]
theorem isOpenImmersion_morNumericalHilbertι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    Quot.IsOpenImmersionOnSchemesOver
      (morNumericalι y x (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
