/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat.PureProjectiveResolution

variable {A : Type u} [CommRing A]
variable {M N : ModuleCat.{v} A}

/-- A module morphism lifts to an augmentation-compatible chain map from a pure projective
resolution to a universally exact resolution. -/
@[stacks 0703]
theorem existsLift (P : ModuleCat.PureProjectiveResolution M)
    (Q : ModuleCat.UniversallyExactResolution N) (f : M ⟶ N) :
    ∃ φ : P.complex ⟶ Q.complex, φ.f 0 ≫ Q.π = P.π ≫ f := sorry

/-- Two augmentation-compatible lifts of the same module morphism from a pure projective
resolution to a universally exact resolution are chain homotopic. -/
@[stacks 0703]
theorem homotopyOfLifts (P : ModuleCat.PureProjectiveResolution M)
    (Q : ModuleCat.UniversallyExactResolution N) (f : M ⟶ N)
    (α β : P.complex ⟶ Q.complex)
    (hα : α.f 0 ≫ Q.π = P.π ≫ f) (hβ : β.f 0 ≫ Q.π = P.π ≫ f) :
    homotopic (ModuleCat A) (ComplexShape.down ℕ) α β := sorry

end ModuleCat.PureProjectiveResolution
