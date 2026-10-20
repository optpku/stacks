module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.FiniteProducts
import StacksCheckRecall

/-!
# Finite products of trivial square-zero extensions

The functor `Mod_R ⥤ S`-Alg/`R` sending `M` to `R[M]` preserves finite products:
the comparison `R[M × N] ⟶ R[M] ×_R R[N]` is an isomorphism, and `R[0] ≅ R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

namespace TrivSqZeroExt

/- Lemma 90.11.7: The square-zero extension functor `Mod_R ⥤ S`-Alg/`R`
preserves finite products, including binary products and the terminal object. -/
@[stacks 06I9] #check
  (TrivSqZeroExt.overFunctor_preservesFiniteProducts S R :
    PreservesFiniteProducts (TrivSqZeroExt.overFunctor S R))

end TrivSqZeroExt
