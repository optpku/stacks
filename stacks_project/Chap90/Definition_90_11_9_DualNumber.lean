module

public import Mathlib.Algebra.DualNumber
public import stacks_project.Chap90.Lemma_90_11_8_FGOver

/-!
# Dual numbers as objects of `S`-Alg/`R`

The dual-number algebra `R[ε]` is the trivial square-zero extension of the finite
`R`-module `R`, both as an object of `S`-Alg/`R` and as an object of a subcategory
containing every `R[M]`.
-/

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

namespace TrivSqZeroExt

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The dual-number object `R[ε]` of `S`-Alg/`R`, as the trivial square-zero
extension of the finite `R`-module `R`. -/
def dualNumberOver : Over (CommAlgCat.of S R) :=
  (fgOverFunctor S R).obj (FGModuleCat.of R R)

/-- `dualNumberOver` is `fgOverFunctor` evaluated at `FGModuleCat.of R R`. -/
theorem dualNumberOver_eq :
    dualNumberOver S R = (fgOverFunctor S R).obj (FGModuleCat.of R R) := sorry

variable {S R}
variable (P : ObjectProperty (Over (CommAlgCat.of S R)))
variable [P.ContainsFGTrivSqZeroExt]

/-- The dual-number object `R[ε]` of a subcategory of `S`-Alg/`R` containing every
`R[M]`. -/
def dualNumberObj : P.FullSubcategory :=
  (fgLift P).obj (FGModuleCat.of R R)

/-- The underlying object of `dualNumberObj` is `dualNumberOver`. -/
theorem dualNumberObj_obj : (dualNumberObj P).obj = dualNumberOver S R := sorry

end TrivSqZeroExt
