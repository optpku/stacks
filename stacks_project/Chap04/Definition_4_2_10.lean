/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]
variable (P : ObjectProperty C)

/-
The source contains three related notions, but they should not be bundled into a new root-level
`Subcategory` structure.

* An object property `P : ObjectProperty C` chooses the objects.
* A multiplicative `W : MorphismProperty P.FullSubcategory` chooses the arrows between them.
  The resulting category is `WideSubcategory W`, and its inclusion in `C` is the composite of the
  two canonical inclusions.
* In the full case the arrow selector is unnecessary: `P.FullSubcategory` is the canonical owner.
* Strict fullness, usually called repleteness, is exactly the additional class
  `P.IsClosedUnderIsomorphisms`.

Keeping these orthogonal layers visible reuses the mathlib APIs for object properties, morphism
properties, and inclusions without introducing a parallel category wrapper.
-/

/- Definition 4.2.10 (1): after choosing the objects by `P`, a general subcategory is the wide
subcategory determined by a multiplicative morphism property on `P.FullSubcategory`. -/
@[stacks 001D "(1) subcategories from object and morphism properties"]
#check (fun (P : ObjectProperty C) (W : MorphismProperty P.FullSubcategory)
    [W.IsMultiplicative] ↦ WideSubcategory W :
  ∀ (P : ObjectProperty C) (W : MorphismProperty P.FullSubcategory),
    [W.IsMultiplicative] → Type u)

/- Its faithful inclusion into `C` is the composite of the wide-subcategory inclusion with the
full-subcategory inclusion. -/
#check (fun (P : ObjectProperty C) (W : MorphismProperty P.FullSubcategory)
    [W.IsMultiplicative] ↦ wideSubcategoryInclusion W ⋙ P.ι :
  ∀ (P : ObjectProperty C) (W : MorphismProperty P.FullSubcategory),
    [W.IsMultiplicative] → WideSubcategory W ⥤ C)

/- Definition 4.2.10 (2): a full subcategory selected by `P : ObjectProperty C` is the canonical
category `P.FullSubcategory`; no morphism selector is needed. -/
@[stacks 001D "(2) full subcategories"]
#check (P.FullSubcategory : Type u)

/- The full-subcategory inclusion and its fully faithful structure are the canonical elimination
API for the source equality of hom-sets. -/
#check ObjectProperty.ι
#check ObjectProperty.fullyFaithfulι

/- Definition 4.2.10 (3): `P.FullSubcategory` is strictly full, or replete, precisely when `P` is
closed under ambient isomorphisms. -/
@[stacks 001D "(3) strictly full subcategories"]
#check (P.IsClosedUnderIsomorphisms : Prop)

/- Transport of membership across an ambient isomorphism is the elimination API for strict
fullness. -/
#check ObjectProperty.prop_of_iso

end CategoryTheory
