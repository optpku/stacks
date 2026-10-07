module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Complex
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Finite.Construction

/-!
# Complexes Underlying Finite Restrictions of Postnikov Towers

This leaf specializes the generic complex property of a finite Postnikov
system to the canonical finite restriction of a sequential tower.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Finite

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Every finite row cut out from a sequential Postnikov tower is a complex. This specializes
`PostnikovSystem.isComplex` to the canonical finite restriction. -/
@[stacks 0D8Z]
theorem isComplex (T : Tower D) (n : ℕ) :
    (T.row n).IsComplex := sorry

end CategoryTheory.PostnikovSystem.Tower.Finite
