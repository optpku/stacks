/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Closure
public import ReasLib.CategoryTheory.Linear.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

universe w v u

namespace CategoryTheory.BrownRepresentability

/-- A finite-dimensional `k`-linear cohomological functor on the compact objects of a
compactly generated `k`-linear triangulated category is naturally isomorphic to the
linear Yoneda functor of an ambient object, restricted to compact objects. -/
theorem existsRepresentationOnCompacts
    {k : Type w} [Field k] {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v} D]
    (hD : IsCompactlyGenerated D)
    (H : (compactObjectSubcategory D)ᵒᵖ ⥤ ModuleCat.{v} k) [H.IsHomological] [H.Linear k]
    [∀ X : compactObjectSubcategory D, Module.Finite k (H.obj (op X))] :
    ∃ Y : D, Nonempty ((ObjectProperty.ι (IsCompactObject : ObjectProperty D)).op ⋙
      (linearYoneda k D).obj Y ≅ H) := sorry

end CategoryTheory.BrownRepresentability
