/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion
public import stacks_project.Chap108.Lemma_108_4_6_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap108.Lemma_108_4_8_Flat
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Substack

/-!
# Lemma 108.4.8

In Situation 108.4.7 the stack `Coh^P_{X/B}` is algebraic and the inclusion
`Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is a flat closed immersion. If `I` is
finite or `B` is locally Noetherian, that inclusion is also an open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.4.8 (1): in Situation 108.4.7 the stack `Coh^P_{X/B}` is
algebraic. -/
@[stacks 0DND]
instance instAlgebraicStack_toGroupoidsNumerical (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    AlgebraicStack (toGroupoidsNumerical f E P hE) :=
  sorry

/-- Lemma 108.4.8 (2): the inclusion `Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is
flat. -/
@[stacks 0DND]
instance instFlat_ι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Hom.Flat (Numerical.ι f E P hE) :=
  sorry

/-- Lemma 108.4.8 (3): the inclusion `Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is
a closed immersion. -/
@[stacks 0DND]
instance instClosedImmersion_ι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Hom.ClosedImmersion (Numerical.ι f E P hE) :=
  sorry

/-- Lemma 108.4.8 (4): if `I` is finite, then the inclusion
`Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is an open immersion. -/
@[stacks 0DND]
instance instOpenImmersion_ι_of_finite (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} [Finite I] (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Hom.OpenImmersion (Numerical.ι f E P hE) :=
  sorry

/-- Lemma 108.4.8 (5): if `B` is locally Noetherian, then the inclusion
`Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is an open immersion. -/
@[stacks 0DND]
instance instOpenImmersion_ι_of_locallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    Hom.OpenImmersion (Numerical.ι f E P hE) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
