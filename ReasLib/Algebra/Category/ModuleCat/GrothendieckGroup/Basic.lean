/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck Groups of Modules

@stack 00JH

This file specializes the property-indexed Grothendieck-group construction to finitely generated
modules and finitely generated projective modules.  The notation `K0` is a namespace, not a new
unqualified global family of declarations.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [Ring R]

/-- The projective Grothendieck group `K₀(R)`. -/
@[stacks 00JH "projective Grothendieck group"]
abbrev projective : Type (max u (v + 1)) :=
  ObjectProperty.GrothendieckGroup (ModuleCat.finiteProjective.{u, v} R)

/-- The class of a finitely generated projective module in `K₀(R)`. -/
@[stacks 00JH "projective Grothendieck class"]
abbrev projectiveOf (M : ModuleCat.FiniteProjective.{u, v} R) : projective.{u, v} R :=
  ObjectProperty.GrothendieckGroup.of (ModuleCat.finiteProjective.{u, v} R) M

/-- The finite-module Grothendieck group `K'_0(R)`. -/
@[stacks 00JH "finite-module Grothendieck group"]
abbrev finite : Type (max u (v + 1)) :=
  ObjectProperty.GrothendieckGroup (ModuleCat.isFG.{v} R)

/-- The class of a finitely generated module in `K'_0(R)`. -/
@[stacks 00JH "finite-module Grothendieck class"]
abbrev finiteOf (M : FGModuleCat.{v} R) : finite.{u, v} R :=
  ObjectProperty.GrothendieckGroup.of (ModuleCat.isFG.{v} R) M

/-- The class of an unbundled finitely generated module in `K'_0(R)`. -/
@[stacks 00JH "unbundled finite-module Grothendieck class"]
abbrev finiteClass (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : finite.{u, v} R :=
  finiteOf R (FGModuleCat.of R M)

/-- The zero module has trivial class in the Grothendieck group of any module property containing
it. -/
@[stacks 00JH "zero module Grothendieck class"]
theorem of_zero {P : ObjectProperty (ModuleCat.{v} R)}
    (h0 : P (ModuleCat.of R PUnit)) :
    ObjectProperty.GrothendieckGroup.of P ⟨ModuleCat.of R PUnit, h0⟩ = 0 := sorry

/-- Isomorphic modules have the same class when the module property contains the zero module. -/
@[stacks 00JH "isomorphic module Grothendieck classes"]
theorem of_iso {P : ObjectProperty (ModuleCat.{v} R)}
    (h0 : P (ModuleCat.of R PUnit)) {M N : P.FullSubcategory} (e : M ≅ N) :
    ObjectProperty.GrothendieckGroup.of P M = ObjectProperty.GrothendieckGroup.of P N := sorry

/-- A subsingleton module has trivial class in every property-indexed module Grothendieck group. -/
@[stacks 00JH "subsingleton module Grothendieck class"]
theorem of_subsingleton {P : ObjectProperty (ModuleCat.{v} R)}
    (M : P.FullSubcategory) [Subsingleton M.obj] :
    ObjectProperty.GrothendieckGroup.of P M = 0 := sorry

/-- The canonical comparison map `K₀(R) → K'_0(R)` induced by forgetting projectivity. -/
@[stacks 00JH "projective-to-finite Grothendieck comparison"]
def projectiveToFinite : projective.{u, v} R →+ finite.{u, v} R :=
  ObjectProperty.GrothendieckGroup.map (ModuleCat.finiteProjective_le_isFG.{u, v} R)

/-- The comparison map sends a finite-projective generator to the class of its underlying finite
module. -/
@[simp]
theorem projectiveToFinite_of (M : ModuleCat.FiniteProjective.{u, v} R) :
    projectiveToFinite.{u, v} R (projectiveOf.{u, v} R M) =
      finiteOf.{u, v} R
        ((ObjectProperty.ιOfLE (ModuleCat.finiteProjective_le_isFG.{u, v} R)).obj M) := sorry

end CategoryTheory.ModuleCat.K0
