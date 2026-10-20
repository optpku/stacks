/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.FiniteDimensional
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

universe w v u

namespace CategoryTheory.BrownRepresentability

/- Lemma 57.6.2: A finite-dimensional `k`-linear cohomological functor on the compact
objects of a compactly generated `k`-linear triangulated category is represented by an
ambient object, through the linear Yoneda functor restricted to compact objects. -/
@[stacks 0FYG] #check (CategoryTheory.BrownRepresentability.existsRepresentationOnCompacts :
  ∀
    {k : Type w} [Field k] {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v} D]
    (hD : IsCompactlyGenerated D)
    (H : (compactObjectSubcategory D)ᵒᵖ ⥤ ModuleCat.{v} k) [H.IsHomological] [H.Linear k]
    [∀ X : compactObjectSubcategory D, Module.Finite k (H.obj (op X))],
    ∃ Y : D, Nonempty ((ObjectProperty.ι (IsCompactObject : ObjectProperty D)).op ⋙
      (linearYoneda k D).obj Y ≅ H))

end CategoryTheory.BrownRepresentability
