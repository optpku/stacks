/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Products supported on a subtype

If every factor of a product outside a predicate is a zero object, the full product is
canonically isomorphic to the product over the corresponding subtype.  This file exposes both
directions and their projection formulas, so downstream finite-support arguments can use the
comparison without rebuilding product extensionality proofs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits.Pi

variable {C : Type u} [Category.{v} C]
variable {ι : Type w}

/-- Restrict a product to the factors satisfying `p`. -/
@[stacks 016R "restriction of an indexed product"]
noncomputable def restrict (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)] :
    ∏ᶜ X ⟶ ∏ᶜ Subtype.restrict p X :=
  Pi.lift fun i ↦ Pi.π X i.1

/-- The component used to extend a restricted product by its uniquely determined maps to the
zero factors outside `p`. -/
noncomputable def extendComponent (X : ι → C) (p : ι → Prop)
    [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) (i : ι) :
    (∏ᶜ Subtype.restrict p X) ⟶ X i :=
  @dite ((∏ᶜ Subtype.restrict p X) ⟶ X i) (p i)
    (Classical.propDecidable (p i))
    (fun hi ↦ Pi.π (Subtype.restrict p X) ⟨i, hi⟩)
    (fun hi ↦ (h i hi).from_ _)

/-- Extend a product over a subtype to the full product when all omitted factors are zero. -/
@[stacks 016R "extension of a supported indexed product"]
noncomputable def extend (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) :
    (∏ᶜ Subtype.restrict p X) ⟶ ∏ᶜ X :=
  Pi.lift (extendComponent X p h)

/-- Restriction followed by a subtype projection is the corresponding full-product
projection. -/
@[reassoc (attr := simp), stacks 016R "restriction projection formula"]
theorem restrict_π (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)] (i : Subtype p) :
    restrict X p ≫ Pi.π (Subtype.restrict p X) i = Pi.π X i.1 := sorry

/-- Extension followed by a full-product projection is its prescribed supported component. -/
@[reassoc (attr := simp), stacks 016R "extension projection formula"]
theorem extend_π (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) (i : ι) :
    extend X p h ≫ Pi.π X i = extendComponent X p h i := sorry

/-- Deleting zero factors outside `p` identifies the full product with the product over the
subtype cut out by `p`. -/
@[stacks 016R "product supported on a subtype"]
noncomputable def isoSubtypeOfIsZero (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) :
    ∏ᶜ X ≅ ∏ᶜ Subtype.restrict p X where
  hom := restrict X p
  inv := extend X p h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `isoSubtypeOfIsZero` is product restriction. -/
@[simp]
theorem isoSubtypeOfIsZero_hom (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) :
    (isoSubtypeOfIsZero X p h).hom = restrict X p := sorry

/-- The inverse map of `isoSubtypeOfIsZero` is extension through the zero factors. -/
@[simp]
theorem isoSubtypeOfIsZero_inv (X : ι → C) (p : ι → Prop)
    [HasProduct X] [HasProduct (Subtype.restrict p X)]
    (h : ∀ i, ¬ p i → IsZero (X i)) :
    (isoSubtypeOfIsZero X p h).inv = extend X p h := sorry

end CategoryTheory.Limits.Pi
