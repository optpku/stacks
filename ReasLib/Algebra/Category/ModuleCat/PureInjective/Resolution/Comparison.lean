/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat.PureInjectiveCoresolution

variable {A : Type u} [CommRing A]
variable {M N : ModuleCat.{v} A}

/-- A module morphism extends to an augmentation-compatible cochain map from a universally
exact coresolution to a pure injective coresolution. -/
theorem existsLift (P : ModuleCat.UniversallyExactCoresolution M)
    (I : ModuleCat.PureInjectiveCoresolution N) (f : M ⟶ N) :
    ∃ φ : P.cocomplex ⟶ I.cocomplex, P.ι ≫ φ.f 0 = f ≫ I.ι := sorry

/-- Two augmentation-compatible extensions of the same module morphism from a universally
exact coresolution to a pure injective coresolution are cochain homotopic. -/
theorem homotopyOfLifts (P : ModuleCat.UniversallyExactCoresolution M)
    (I : ModuleCat.PureInjectiveCoresolution N) (f : M ⟶ N)
    (α β : P.cocomplex ⟶ I.cocomplex)
    (hα : P.ι ≫ α.f 0 = f ≫ I.ι) (hβ : P.ι ≫ β.f 0 = f ≫ I.ι) :
    homotopic (ModuleCat A) (ComplexShape.up ℕ) α β := sorry

end ModuleCat.PureInjectiveCoresolution
