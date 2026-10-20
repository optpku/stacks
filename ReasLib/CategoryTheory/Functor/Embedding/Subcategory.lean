/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
public import ReasLib.CategoryTheory.Functor.Embedding

/-!
# Embeddings of canonical subcategories

This file records the equality-sensitive embedding instances for the standard full- and
wide-subcategory inclusions. They are separated from the core predicate so users of
`Functor.IsEmbedding` do not need to import either subcategory construction.
-/

@[expose] public section

namespace CategoryTheory

universe v u

namespace ObjectProperty.FullSubcategory

variable {C : Type u} [Category.{v} C]
variable {P Q : ObjectProperty C}

/-- The canonical inclusion of a full subcategory is an embedding. -/
@[stacks 05QM "embedding of the canonical full-subcategory inclusion"]
instance ιIsEmbedding (P : ObjectProperty C) : P.ι.IsEmbedding := sorry

/-- The inclusion of full subcategories induced by `P ≤ Q` is an embedding. -/
@[stacks 05QM "embedding of the inclusion induced by a subcategory inclusion"]
instance ιOfLEIsEmbedding (h : P ≤ Q) : (ObjectProperty.ιOfLE h).IsEmbedding := sorry

end ObjectProperty.FullSubcategory

namespace WideSubcategory

variable {C : Type u} [Category.{v} C]

/-- The canonical inclusion of a wide subcategory is an embedding. -/
@[stacks 05QM "embedding of the canonical wide-subcategory inclusion"]
instance inclusionIsEmbedding (W : MorphismProperty C) [W.IsMultiplicative] :
    (wideSubcategoryInclusion W).IsEmbedding := sorry

end WideSubcategory

end CategoryTheory
