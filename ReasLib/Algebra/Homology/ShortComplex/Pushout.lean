module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

/-- A pushout of a short exact complex along its first map remains short exact when
the induced projection to the original cokernel is compatible with the pushout square. -/
theorem shortExact_of_isPushout
    {C : Type u} [Category.{v} C] [Abelian C] {K P K' E M : C}
    (ι : K ⟶ P) (π : P ⟶ M) (hιπ : ι ≫ π = 0)
    (h : (ShortComplex.mk ι π hιπ).ShortExact) (φ : K ⟶ K')
    (j : P ⟶ E) (ι' : K' ⟶ E) (hE : IsPushout ι φ j ι') (π' : E ⟶ M)
    (hj : j ≫ π' = π) (hι'π' : ι' ≫ π' = 0) :
    (ShortComplex.mk ι' π' hι'π').ShortExact := sorry

end CategoryTheory.ShortComplex
