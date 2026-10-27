/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Numerical.Immersion
import StacksCheckRecall

/-!
# Remark 108.10.4 (Numerical invariants)

The numerical relative-Hom locus is the intersection with the numerical Hilbert
locus. Its canonical inclusion is flat and closed, and is also open for a finite
index type, a locally Noetherian base, or all integral powers of an invertible
module. The latter specialization is `morNumericalHilbert`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/- Remark 108.10.4 (Numerical invariants) (1) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumerical :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Subfunctor (mor y x))

/- Remark 108.10.4 (Numerical invariants) (2) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isClosedImmersion_morNumericalι :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    SchemeOver.IsClosedImmersion (morNumericalι y x E P hE))

/- Remark 108.10.4 (Numerical invariants) (3) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isFlat_morNumericalι :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    SchemeOver.IsFlat (morNumericalι y x E P hE))

/- Remark 108.10.4 (Numerical invariants) (4) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isOpenImmersion_morNumericalι_of_finite :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} [Finite I] (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE))

/- Remark 108.10.4 (Numerical invariants) (5) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isOpenImmersion_morNumericalι_of_locallyNoetherian :
    ∀ (y : Y ⟶ B)
    (x : X ⟶ B) [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B],
    Quot.IsOpenImmersionOnSchemesOver (morNumericalι y x E P hE))

/- Remark 108.10.4 (Numerical invariants) (6) -/
@[stacks 0DPQ] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isOpenImmersion_morNumericalHilbertι :
    ∀ (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    Quot.IsOpenImmersionOnSchemesOver
      (morNumericalι y x (Quot.invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L)))

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
