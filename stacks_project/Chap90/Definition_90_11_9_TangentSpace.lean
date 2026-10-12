/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_11_9_DualNumber
public import stacks_project.Chap90.Lemma_90_11_8_Eval

/-!
# Tangent space of a set-valued functor

The tangent space `TF` of a functor `F` on a strictly full subcategory of
`S`-Alg/`R` containing every `R[M]`, with `F(R)` a singleton, is the value
`F(R[ε])`.
-/

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

namespace TrivSqZeroExt

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
variable (F : P.FullSubcategory ⥤ Type u)

/-- The tangent space of a set-valued functor is its value at the dual-number
object `R[ε]`. -/
def tangentSpace [Unique (F.obj (overSelfObj P))] : Type u :=
  F.obj (dualNumberObj P)

/-- The tangent space is the value of `F` at `dualNumberObj`. -/
theorem tangentSpace_def [Unique (F.obj (overSelfObj P))] :
    tangentSpace F = F.obj (dualNumberObj P) := sorry

/-- The tangent space is `fgEval` at the finite `R`-module `R`. -/
theorem tangentSpace_fgEval [Unique (F.obj (overSelfObj P))] :
    tangentSpace F = (Functor.fgEval P F).obj (FGModuleCat.of R R) := sorry

end TrivSqZeroExt
