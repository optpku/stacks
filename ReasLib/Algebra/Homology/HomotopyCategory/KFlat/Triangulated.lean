module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated K-flat objects in the homotopy category

K-flat objects form a triangulated object property in the homotopy category. Applications to
modules or sheaves should specialize this owner instead of introducing parallel closure APIs.

@stack 06Y2
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalPreadditive C]

namespace KFlat

/-- K-flat objects form a triangulated object property. -/
@[stacks 06Y2 "triangulated object property"]
instance isTriangulated :
    (HomotopyCategory.kFlat C).IsTriangulated := sorry

end KFlat

namespace IsKFlat

/-- In a distinguished triangle, K-flatness of the first two objects implies K-flatness of the
third. -/
@[stacks 06Y2 "third object"]
theorem obj₃_of_distinguished
    (T : Triangle (HomotopyCategory C (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory C (up ℤ)))
    (h₁ : T.obj₁.IsKFlat) (h₂ : T.obj₂.IsKFlat) :
    T.obj₃.IsKFlat := sorry

/-- In a distinguished triangle, K-flatness of the first and third objects implies K-flatness of
the second. -/
@[stacks 06Y2 "second object"]
theorem obj₂_of_distinguished
    (T : Triangle (HomotopyCategory C (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory C (up ℤ)))
    (h₁ : T.obj₁.IsKFlat) (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := sorry

/-- In a distinguished triangle, K-flatness of the last two objects implies K-flatness of the
first. -/
@[stacks 06Y2 "first object"]
theorem obj₁_of_distinguished
    (T : Triangle (HomotopyCategory C (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory C (up ℤ)))
    (h₂ : T.obj₂.IsKFlat) (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := sorry

end IsKFlat

end CategoryTheory.HomotopyCategory
