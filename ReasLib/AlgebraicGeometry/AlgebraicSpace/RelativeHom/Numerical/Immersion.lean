/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Numerical.Immersion

/-! # Geometric properties of numerical relative-Hom loci -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- The inclusion of the numerical relative-Hom locus is a closed immersion. -/
theorem isClosedImmersion_morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsClosedImmersion (morNumericalι y x E P hE) := sorry

/-- The inclusion of the numerical relative-Hom locus is flat. -/
theorem isFlat_morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsFlat (morNumericalι y x E P hE) := sorry

/-- The inclusion of the numerical relative-Hom locus is an open immersion when the
index type of the perfect family is finite. -/
theorem isOpenImmersion_morNumericalι_of_finite (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} [Finite I] (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE) := sorry

/-- The inclusion of the numerical relative-Hom locus is an open immersion over a
locally Noetherian base. -/
theorem isOpenImmersion_morNumericalι_of_locallyNoetherian (y : Y ⟶ B)
    (x : X ⟶ B) [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE) := sorry

/-- The inclusion of the numerical relative-Hom locus defined by all integral powers
of an invertible module is an open immersion. -/
theorem isOpenImmersion_morNumericalHilbertι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    Quot.IsOpenImmersionOnSchemesOver
      (morNumericalι y x (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
