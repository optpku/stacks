module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Substacks and essential images of immersions

Substacks are replete full subcategories whose restricted projections are
algebraic stacks and whose literal inclusions have the specified immersion property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {Z X : GroupoidsOver S}

namespace Substack

/-- Restrict a groupoid fibration to a full subcategory whose projection is
fibred in groupoids. -/
def category (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)) : GroupoidsOver S :=
  ofFunctor (P.ι ⋙ X.p) (h := h)

/-- The literal inclusion of a full subcategory into its ambient groupoid fibration. -/
def inclusion (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)) : category X P h ⟶ X :=
  ofBasedFunctor { toFunctor := P.ι, w := rfl }

/-- The projection of the restricted groupoid fibration is the restricted projection. -/
@[simp]
theorem category_p (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)) :
    (category X P h).p = P.ι ⋙ X.p := rfl

/-- The total functor of the inclusion is the literal full-subcategory inclusion. -/
@[simp]
theorem inclusion_toFunctor (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)) :
    toFunctor (inclusion X P h) = P.ι := rfl

/-- An object property defines a locally closed substack when it is closed under
isomorphisms and its full subcategory is an algebraic stack with immersion inclusion. -/
def IsLocallyClosed (X : GroupoidsOver S) (P : ObjectProperty X.total) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p),
      AlgebraicStack (category X P h) ∧ Immersion (inclusion X P h)

/-- An object property defines a closed substack when it is closed under
isomorphisms and its full subcategory is an algebraic stack with closed immersion inclusion. -/
def IsClosed (X : GroupoidsOver S) (P : ObjectProperty X.total) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p),
      AlgebraicStack (category X P h) ∧ ClosedImmersion (inclusion X P h)

/-- An object property defines an open substack when it is closed under
isomorphisms and its full subcategory is an algebraic stack with open immersion inclusion. -/
def IsOpen (X : GroupoidsOver S) (P : ObjectProperty X.total) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p),
      AlgebraicStack (category X P h) ∧ OpenImmersion (inclusion X P h)

/-- A morphism has image given by an object property if it factors, up to
2-isomorphism, through the literal full-subcategory inclusion by an equivalence over the base. -/
def IsImage (i : Z ⟶ X) (P : ObjectProperty X.total) : Prop :=
  ∃ (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)) (j : Z ⟶ category X P h),
    (toBasedFunctor j).IsEquivalence ∧ Nonempty (j ≫ inclusion X P h ≅ i)

end Substack

/-- The essential image of an immersion of algebraic stacks is locally closed,
admits an equivalence factorization, and is the unique locally closed object
property admitting such a factorization. -/
theorem existsUnique_image [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [Immersion i] :
    Substack.IsLocallyClosed X (toFunctor i).essImage ∧
      Substack.IsImage i (toFunctor i).essImage ∧
        ∀ P : ObjectProperty X.total,
          Substack.IsLocallyClosed X P → Substack.IsImage i P →
            P = (toFunctor i).essImage := sorry

/-- The essential image of a closed immersion of algebraic stacks is a closed substack. -/
theorem image_isClosed [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [ClosedImmersion i] :
    Substack.IsClosed X (toFunctor i).essImage := sorry

/-- The essential image of an open immersion of algebraic stacks is an open substack. -/
theorem image_isOpen [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [OpenImmersion i] :
    Substack.IsOpen X (toFunctor i).essImage := sorry

end AlgebraicGeometry.AlgebraicStack
