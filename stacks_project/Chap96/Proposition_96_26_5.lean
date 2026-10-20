/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.FormalSpectrum
import StacksCheckRecall

/-! # Quasi-coherent derived objects on an adic Noetherian formal spectrum -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 96.26.5: quasi-coherent derived objects on the fibration associated to
`Spf(A)` are canonically equivalent to the `I`-derived-complete objects of `D(A)`. -/
@[stacks 0H0L] #check (AlgebraicGeometry.GroupoidsOver.toDerivedComplete_isEquivalence :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A] [IsNoetherianRing A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
    (AlgebraicGeometry.GroupoidsOver.toDerivedComplete structureHom I hI).IsEquivalence)
