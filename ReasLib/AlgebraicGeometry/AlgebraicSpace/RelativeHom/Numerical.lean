/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Graph
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Numerical

/-!
# Numerical loci of relative morphisms

The numerical relative-Hom functor `Mor^P_B(Y, X)` is the preimage of
`Hilb^P_{Y ×_B X/B}` along the graph comparison `Mor_B(Y, X) ⟶ Hilb_{Y ×_B X/B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- The structure morphism `(Y ×_B X) ⟶ B` is of finite presentation when
`Y ⟶ B` and `X ⟶ B` are. -/
instance instFinitePresentation_productHom (y : Y ⟶ B) (x : X ⟶ B)
    [FinitePresentation y] [FinitePresentation x] :
    FinitePresentation (productHom y x) := sorry

/-- The structure morphism `(Y ×_B X) ⟶ B` is separated when `Y ⟶ B` and
`X ⟶ B` are. -/
instance instSeparated_productHom (y : Y ⟶ B) (x : X ⟶ B)
    [Separated y] [Separated x] :
    Separated (productHom y x) := sorry

/-- The numerical relative-Hom functor `Mor^P_B(Y, X)`, as the preimage of
`Hilb^P_{Y ×_B X/B}` along `graph`. -/
def morNumerical (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Subfunctor (mor y x) :=
  (Subfunctor.range (Hilbert.hilbertNumericalι (productHom y x) E P hE)).preimage
    (graph y x)

/-- `morNumerical` is the preimage of the numerical Hilbert locus along
`graph`. -/
theorem morNumerical_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    morNumerical y x E P hE =
      (Subfunctor.range (Hilbert.hilbertNumericalι (productHom y x) E P hE)).preimage
        (graph y x) := sorry

/-- A relative morphism lies in `morNumerical` if and only if its graph lies in
the numerical Hilbert locus. -/
theorem mem_morNumerical (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {σ : (SchemeOver B)ᵒᵖ}
    (b : (mor y x).obj σ) :
    b ∈ (morNumerical y x E P hE).obj σ ↔
      (graph y x).app σ b ∈
        Set.range ((Hilbert.hilbertNumericalι (productHom y x) E P hE).app σ) := sorry

/-- The inclusion `Mor^P_B(Y, X) ⟶ Mor_B(Y, X)`. -/
def morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (morNumerical y x E P hE).toFunctor ⟶ mor y x :=
  (morNumerical y x E P hE).ι

/-- `morNumericalι` is the subfunctor inclusion of `morNumerical`. -/
theorem morNumericalι_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    morNumericalι y x E P hE = (morNumerical y x E P hE).ι := sorry

/-- The numerical relative-Hom locus `Mor^{P,L}_B(Y, X)` associated to all integral
powers of an invertible `𝒪_{Y ×_B X}`-module `L` and a function `P : ℤ → ℤ`. -/
abbrev morNumericalHilbert (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :=
  morNumerical y x (Quot.invertiblePowerFamily L) (fun n ↦ P n.down)
    (Quot.isPerfect_invertiblePowerFamily L)

/-- `morNumericalHilbert` is `morNumerical` of the family `n ↦ L^{⊗ n}`. -/
theorem morNumericalHilbert_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    morNumericalHilbert y x L P =
      morNumerical y x (Quot.invertiblePowerFamily L) (fun n ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
