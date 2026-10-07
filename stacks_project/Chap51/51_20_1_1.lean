module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.ShortComplex.Pushout
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

open CategoryTheory

universe u

variable {R : Type u} [Ring R] (r : ℕ) {K K' E M : ModuleCat.{u} R}

/- 51.20.1.1: pushing the short exact presentation
`0 ⟶ K ⟶ Rⁿ ⟶ M ⟶ 0` out along `K ⟶ K'` gives the short exact sequence
`0 ⟶ K' ⟶ E ⟶ M ⟶ 0`. -/
@[stacks 0G9U] #check
  (CategoryTheory.ShortComplex.shortExact_of_isPushout :
    ∀ (ι : K ⟶ ModuleCat.of R (Fin r → R))
      (π : ModuleCat.of R (Fin r → R) ⟶ M) (hιπ : ι ≫ π = 0)
      (h : (ShortComplex.mk ι π hιπ).ShortExact) (φ : K ⟶ K')
      (j : ModuleCat.of R (Fin r → R) ⟶ E) (ι' : K' ⟶ E)
      (hE : IsPushout ι φ j ι') (π' : E ⟶ M)
      (hj : j ≫ π' = π) (hι'π' : ι' ≫ π' = 0),
      (ShortComplex.mk ι' π' hι'π').ShortExact)
