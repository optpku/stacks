/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.Evaluation

/-!
# Tangent spaces of set-valued functors on square-zero extensions

The dual-number algebra is the rank-one square-zero extension. The tangent space
of a set-valued functor with singleton value at the base algebra is its value at
this dual-number object.
-/

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

namespace TrivSqZeroExt

section

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The dual-number object `R[ε]` of `S`-Alg/`R` is the trivial square-zero
extension of the finite `R`-module `R`. -/
def dualNumberOver : Over (CommAlgCat.of S R) :=
  (fgOverFunctor S R).obj (FGModuleCat.of R R)

/-- The dual-number object is the square-zero extension functor evaluated at
the rank-one `R`-module `R`. -/
theorem dualNumberOver_eq :
    dualNumberOver S R = (fgOverFunctor S R).obj (FGModuleCat.of R R) := sorry

variable {S R}
variable (P : ObjectProperty (Over (CommAlgCat.of S R)))
variable [P.ContainsFGTrivSqZeroExt]

/-- The dual-number object `R[ε]` belongs to a full subcategory of `S`-Alg/`R`
containing the square-zero extensions of all finitely generated `R`-modules. -/
def dualNumberObj : P.FullSubcategory :=
  (fgLift P).obj (FGModuleCat.of R R)

/-- The underlying ambient object of the dual-number object in a full
subcategory is the dual-number object of `S`-Alg/`R`. -/
theorem dualNumberObj_obj : (dualNumberObj P).obj = dualNumberOver S R := sorry

end

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
variable (F : P.FullSubcategory ⥤ Type u)

/-- The tangent space of a set-valued functor on a strictly full subcategory of
`S`-Alg/`R` containing every finitely generated square-zero extension, with
singleton value at `R`, is its value at the dual-number object `R[ε]`. -/
def tangentSpace [Unique (F.obj (overSelfObj P))] : Type u :=
  F.obj (dualNumberObj P)

/-- The tangent space is the value of the functor at the dual-number object. -/
theorem tangentSpace_def [Unique (F.obj (overSelfObj P))] :
    tangentSpace F = F.obj (dualNumberObj P) := sorry

/-- The tangent space is the square-zero evaluation functor evaluated at the
rank-one `R`-module `R`. -/
theorem tangentSpace_fgEval [Unique (F.obj (overSelfObj P))] :
    tangentSpace F = (Functor.fgEval P F).obj (FGModuleCat.of R R) := sorry

end TrivSqZeroExt
