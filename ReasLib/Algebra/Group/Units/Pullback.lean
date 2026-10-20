/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# The cartesian units square

For a monoid homomorphism `f : R →* S`, the square formed by the units inclusions is cartesian
exactly when `f` reflects units.  The construction belongs at the monoid level; ringed-site and
stalk APIs can specialize it without rebuilding a set-theoretic pullback.
-/

@[expose] public section

universe u v

namespace Units.Square

variable {R : Type u} {S : Type v} [Monoid R] [Monoid S]

/-- The set-theoretic pullback of `Sˣ → S` along a monoid homomorphism `f : R →* S`. -/
def Pullback (f : R →* S) :=
  { x : Sˣ × R // (x.1 : S) = f x.2 }

/-- The canonical comparison from the units of the source to the pullback of the units square. -/
def comparison (f : R →* S) : Rˣ → Pullback f :=
  fun x ↦ ⟨⟨Units.map f x, (x : R)⟩, rfl⟩

/-- The units square of `f` is cartesian when its canonical comparison is bijective. -/
def IsCartesian (f : R →* S) : Prop :=
  Function.Bijective (comparison f)

/-- The units square is cartesian exactly when the
homomorphism reflects units. -/
@[stacks 04H9 "algebraic units-square criterion"]
theorem isCartesian_iff_isLocalHom (f : R →* S) :
    IsCartesian f ↔ IsLocalHom f := sorry

end Units.Square
