/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Embedding.Subcategory
import ReasLib.CategoryTheory.Pretriangulated.Subcategory
import StacksCheckRecall

@[expose] public section

/-!
# Pretriangulated Subcategories

The source notion need not be full.  Its reusable formalization is an equality-sensitive
embedding of pretriangulated categories which commutes with shifts and preserves distinguished
triangles.  Full subcategories cut out by triangulated object properties form a canonical
special case.
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {D' : Type u₁} {D : Type u₂} [Category.{v₁} D'] [Category.{v₂} D]
  [Limits.HasZeroObject D'] [Limits.HasZeroObject D]
  [HasShift D' ℤ] [HasShift D ℤ] [Preadditive D'] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D'] [Pretriangulated D]
  (ι : D' ⥤ D) [ι.IsEmbedding] [ι.CommShift ℤ] [ι.IsTriangulated]

/- Definition 13.3.4: a pretriangulated subcategory is presented by a functor injective on
objects and faithful on morphisms, equipped with a comparison with every shift, which sends its
distinguished triangles to distinguished triangles of the ambient category. -/
@[stacks 05QM "subcategory embedding"] #check (inferInstance : ι.IsEmbedding)
@[stacks 05QM "compatibility with shifts"] #check (inferInstance : ι.CommShift ℤ)
@[stacks 05QM "preservation of distinguished triangles"] #check
  (inferInstance : ι.IsTriangulated)

/- Exactness already supplies the additive compatibility of the inclusion; it is not an
independent assumption in the canonical API. -/
#check (inferInstance : ι.Additive)
#check @Functor.map_distinguished

section Triangulated

variable [IsTriangulated D']

/- Definition 13.3.4: when the source pretriangulated category is triangulated, it presents a
triangulated subcategory.  This condition remains explicit; it does not follow merely from a
faithful exact embedding into a triangulated category. -/
@[stacks 05QM "triangulated subcategory"] #check (inferInstance : IsTriangulated D')

end Triangulated

namespace ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/- Full-subcategory companion: a triangulated object property canonically induces the source
pretriangulated structure and an exact embedding into the ambient category. -/
@[stacks 05QM "full subcategory specialization"] #check
  (inferInstance : Pretriangulated P.FullSubcategory)
#check (inferInstance : P.ι.IsEmbedding)
#check (inferInstance : P.ι.IsTriangulated)

/- Reflection of distinguished triangles is available for this full specialization, but is not
part of the general non-full definition. -/
#check @Functor.map_distinguished_iff

variable [IsTriangulated C]

#check (inferInstance : IsTriangulated P.FullSubcategory)

end ObjectProperty

end CategoryTheory
