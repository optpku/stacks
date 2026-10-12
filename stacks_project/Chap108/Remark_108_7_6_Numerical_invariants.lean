/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_5_6_Map
public import stacks_project.Chap108.Remark_108_7_6_Numerical_invariants_Locus
import StacksCheckRecall

/-!
# Remark 108.7.6 (Numerical invariants)

The numerical Hilbert functor `Hilb^P_{X/B}` is `Quot^P_{𝒪_X/X/B}`. The
morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion, and an open
immersion if `I` is finite, or `B` is locally Noetherian, or the family is
`n ↦ L^{⊗ n}` for invertible `L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hilbert
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 108.7.6 (Numerical invariants) (1) -/
@[stacks 0DPG] #check hilbertNumerical

/-- Remark 108.7.6 (Numerical invariants) (2): the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a closed immersion. -/
@[stacks 0DPG]
theorem isClosedImmersion_hilbertNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsClosedImmersionOnSchemesOver (hilbertNumericalι f E P hE) :=
  sorry

/-- Remark 108.7.6 (Numerical invariants) (3): the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is flat. -/
@[stacks 0DPG]
theorem isFlat_hilbertNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsFlatOnSchemesOver (hilbertNumericalι f E P hE) :=
  sorry

/-- Remark 108.7.6 (Numerical invariants) (4): if `I` is finite, then the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG]
theorem isOpenImmersion_hilbertNumericalι_of_finite (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u} [Finite I]
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE) :=
  sorry

/-- Remark 108.7.6 (Numerical invariants) (5): if `B` is locally Noetherian, then
the morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG]
theorem isOpenImmersion_hilbertNumericalι_of_locallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE) :=
  sorry

/-- Remark 108.7.6 (Numerical invariants) (6): if `E n = L^{⊗ n}` for an
invertible `𝒪_X`-module `L`, then the morphism
`Hilb^{P,L}_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG]
theorem isOpenImmersion_hilbertNumericalHilbertι (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Quot.IsOpenImmersionOnSchemesOver
      (hilbertNumericalι f (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
