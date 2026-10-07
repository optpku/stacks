module

public import ReasLib.CategoryTheory.ComposableArrows.Complex
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Factorization

/-!
# Underlying Complexes of Postnikov Systems

Every finite Postnikov system canonically witnesses that its underlying composable row has
square-zero consecutive maps.  This is the general owner of that fact; constructions of
particular Postnikov systems should use it instead of reproving complexness.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

/-- The underlying composable row of a Postnikov system is a complex. -/
@[stacks 0D7Z "underlying complex of a finite Postnikov system"]
theorem isComplex {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) :
    X.IsComplex := sorry

end CategoryTheory.PostnikovSystem
