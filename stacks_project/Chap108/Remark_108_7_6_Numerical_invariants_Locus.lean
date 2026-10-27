/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Numerical
public import stacks_project.Chap108.Remark_108_5_9_Numerical_invariants_Locus

/-! # Numerical Hilbert loci and their defining formulas -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumerical :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Subfunctor (Quot.quot f (SheafOfModules.unit (structureSheaf X))))

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumerical_eq :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    hilbertNumerical f E P hE =
      Quot.quotNumerical f (SheafOfModules.unit (structureSheaf X)) E P hE)

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumericalι :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    (hilbertNumerical f E P hE).toFunctor ⟶ hilbert f)

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumericalι_eq :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    hilbertNumericalι f E P hE =
      Quot.quotNumericalι f (SheafOfModules.unit (structureSheaf X)) E P hE ≫
        (quotIso f).inv)

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumericalι_comp_quotIso :
  ∀ (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    hilbertNumericalι f E P hE ≫ (quotIso f).hom =
      Quot.quotNumericalι f (SheafOfModules.unit (structureSheaf X)) E P hE)

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumericalHilbert :
  ∀ (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    Subfunctor (Quot.quot f (SheafOfModules.unit (structureSheaf X))))

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertNumericalHilbert_eq :
  ∀ (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    hilbertNumericalHilbert f L P =
      hilbertNumerical f (Quot.invertiblePowerFamily L)
        (fun n ↦ P n.down) (Quot.isPerfect_invertiblePowerFamily L))

end AlgebraicGeometry.AlgebraicSpace.Hilbert
