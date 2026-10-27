/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Numerical

/-! # Numerical loci of relative morphisms

Typed compatibility checks for the numerical relative-Hom construction, its
canonical inclusion, and the specialization to integral powers of an invertible
module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.instFinitePresentation_productHom :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [FinitePresentation y] [FinitePresentation x],
    FinitePresentation (productHom y x))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.instSeparated_productHom :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Separated y] [Separated x],
    Separated (productHom y x))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumerical :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Subfunctor (mor y x))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumerical_eq :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    morNumerical y x E P hE =
      (Subfunctor.range (Hilbert.hilbertNumericalι (productHom y x) E P hE)).preimage
        (graph y x))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.mem_morNumerical :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {σ : (SchemeOver B)ᵒᵖ}
    (b : (mor y x).obj σ),
    b ∈ (morNumerical y x E P hE).obj σ ↔
      (graph y x).app σ b ∈
        Set.range ((Hilbert.hilbertNumericalι (productHom y x) E P hE).app σ))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumericalι :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    (morNumerical y x E P hE).toFunctor ⟶ mor y x)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumericalι_eq :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    morNumericalι y x E P hE = (morNumerical y x E P hE).ι)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumericalHilbert :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    Subfunctor (mor y x))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumericalHilbert_eq :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    morNumericalHilbert y x L P =
      morNumerical y x (Quot.invertiblePowerFamily L) (fun n ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L))

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
