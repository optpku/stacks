/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Numerical.Immersion

/-! # Geometric properties of numerical Hilbert loci -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a closed immersion. -/
theorem isClosedImmersion_hilbertNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsClosedImmersion (hilbertNumericalι f E P hE) := sorry

/-- The morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is flat. -/
theorem isFlat_hilbertNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsFlat (hilbertNumericalι f E P hE) := sorry

/-- If `I` is finite, then the morphism
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
theorem isOpenImmersion_hilbertNumericalι_of_finite (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u} [Finite I]
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE) := sorry

/-- If `B` is locally Noetherian, then
the morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
theorem isOpenImmersion_hilbertNumericalι_of_locallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    Quot.IsOpenImmersionOnSchemesOver (hilbertNumericalι f E P hE) := sorry

/-- If `E n = L^{⊗ n}` for an
invertible `𝒪_X`-module `L`, then the morphism
`Hilb^{P,L}_{X/B} ⟶ Hilb_{X/B}` is an open immersion. -/
theorem isOpenImmersion_hilbertNumericalHilbertι (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Quot.IsOpenImmersionOnSchemesOver
      (hilbertNumericalι f (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
