/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.Immersion
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion

/-!
# Lemma 108.4.8

The prescribed numerical-invariant substack is algebraic, and its canonical
inclusion is a flat closed immersion. It is open when the index set is finite
or the base is locally Noetherian.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

universe u

/- Lemma 108.4.8 (1): in Situation 108.4.7 the stack `Coh^P_{X/B}` is
algebraic. -/
@[stacks 0DND] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instAlgebraicStack :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    AlgebraicStack (toGroupoidsNumerical f E P hE))

/- Lemma 108.4.8 (2): the inclusion `Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is
flat. -/
@[stacks 0DND] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instFlat :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Hom.Flat (Numerical.ι f E P hE))

/- Lemma 108.4.8 (3): the inclusion `Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is
a closed immersion. -/
@[stacks 0DND] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instClosedImmersion :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Hom.ClosedImmersion (Numerical.ι f E P hE))

/- Lemma 108.4.8 (4): if `I` is finite, then the inclusion
`Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is an open immersion. -/
@[stacks 0DND] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instOpenImmersionOfFinite :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} [Finite I] (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Hom.OpenImmersion (Numerical.ι f E P hE))

/- Lemma 108.4.8 (5): if `B` is locally Noetherian, then the inclusion
`Numerical.ι : Coh^P_{X/B} ⟶ Coh_{X/B}` is an open immersion. -/
@[stacks 0DND] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instOpenImmersionOfLocallyNoetherian :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B],
    Hom.OpenImmersion (Numerical.ι f E P hE))
