module

public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import ReasLib.CategoryTheory.Pro.Sequential.Quotient.NatTrans
public import ReasLib.CategoryTheory.Pro.Value
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pro-zero vertices in sequential systems of distinguished triangles

If the third vertex system of a sequential system of distinguished triangles has pro-value zero,
then the natural transformations between the first two vertices represent a pro-isomorphism.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory ZeroObject

universe u v

namespace CategoryTheory.Pro.Sequential.Distinguished.ProZero

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Lemma 13.42.4 (Stacks 0G3C): the first morphisms in a sequential system of distinguished
triangles induce an isomorphism of the associated pro-objects when the third vertex system has
value zero. -/
@[stacks 0G3C]
theorem toHom_isIso
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₃ : HasValue (T ⋙ Triangle.π₃) (0 : D)) :
    IsIso ((Pro.SequentialHom.ofNatTrans
      (Functor.whiskerLeft T Triangle.π₁Toπ₂)).toHom) := sorry

/-- The common-refinement class of the first morphisms has invertible associated pro-morphism. -/
@[stacks 0G3C "common-refinement quotient"]
theorem quotientToHom_isIso
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₃ : HasValue (T ⋙ Triangle.π₃) (0 : D)) :
    IsIso (Pro.SequentialHom.quotientToHom
      (Pro.SequentialHom.Quotient.ofNatTrans
        (Functor.whiskerLeft T Triangle.π₁Toπ₂))) := sorry

/-- The 13.42.4 pro-isomorphism has a concrete inverse representative up to common refinement. -/
@[stacks 0G3C "representative inverse"]
theorem hasRepresentativeInverse
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₃ : HasValue (T ⋙ Triangle.π₃) (0 : D)) :
    (Pro.SequentialHom.ofNatTrans
      (Functor.whiskerLeft T Triangle.π₁Toπ₂)).HasRepresentativeInverse := sorry

end CategoryTheory.Pro.Sequential.Distinguished.ProZero
