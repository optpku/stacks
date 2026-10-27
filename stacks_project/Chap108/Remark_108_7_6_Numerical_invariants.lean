/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Numerical.Immersion
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
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 108.7.6 (Numerical invariants) (1): the numerical Hilbert functor. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumerical :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Subfunctor (Quot.quot f (SheafOfModules.unit (structureSheaf X))))

/- Remark 108.7.6 (Numerical invariants) (2): the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a closed immersion. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isClosedImmersion_hilbertNumericalι :
  ∀ (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    SchemeOver.IsClosedImmersion (hilbertNumericalι f E P hE))

/- Remark 108.7.6 (Numerical invariants) (3): the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is flat. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isFlat_hilbertNumericalι :
  ∀ (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    SchemeOver.IsFlat (hilbertNumericalι f E P hE))

/- Remark 108.7.6 (Numerical invariants) (4): if `I` is finite, then the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isOpenImmersion_hilbertNumericalι_of_finite :
  ∀ (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u} [Finite I]
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE))

/- Remark 108.7.6 (Numerical invariants) (5): if `B` is locally Noetherian, then
the morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isOpenImmersion_hilbertNumericalι_of_locallyNoetherian :
  ∀ (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B],
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE))

/- Remark 108.7.6 (Numerical invariants) (6): if `E n = L^{⊗ n}` for an
invertible `𝒪_X`-module `L`, then the morphism
`Hilb^{P,L}_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
@[stacks 0DPG] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isOpenImmersion_hilbertNumericalHilbertι :
  ∀ (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ),
    Quot.IsOpenImmersionOnSchemesOver
      (hilbertNumericalι f (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)))

end AlgebraicGeometry.AlgebraicSpace.Hilbert
