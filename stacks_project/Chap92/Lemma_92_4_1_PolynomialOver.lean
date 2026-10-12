/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Polynomial algebras and the opposite site C_{B/A}

This leaf owns the property of being a polynomial algebra over a commutative ring, the
slice category of polynomial `A`-algebra maps to `B`, and the opposite chaotic site
`C_{B/A}` used to compute derived lower shriek.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra

/-- An `A`-algebra is polynomial when it is isomorphic to a multivariate polynomial algebra
over `A`. -/
class IsPolynomial (A P : Type u) [CommRing A] [CommRing P] [Algebra A P] : Prop where
  /-- There is an `A`-algebra identification with `MvPolynomial σ A` for some type of
  variables. -/
  exists_repr : ∃ σ : Type u, Nonempty (P ≃ₐ[A] MvPolynomial σ A)

/-- Being a polynomial `A`-algebra is equivalent to the existence of a multivariate
polynomial presentation. -/
theorem IsPolynomial.iff (A P : Type u) [CommRing A] [CommRing P] [Algebra A P] :
    IsPolynomial A P ↔ ∃ σ : Type u, Nonempty (P ≃ₐ[A] MvPolynomial σ A) :=
  sorry

end Algebra

namespace MvPolynomial

/-- Multivariate polynomial algebras are polynomial algebras. -/
instance instIsPolynomial {A : Type u} [CommRing A] {σ : Type u} :
    Algebra.IsPolynomial A (MvPolynomial σ A) where
  exists_repr := ⟨σ, ⟨AlgEquiv.refl⟩⟩

end MvPolynomial

namespace Algebra

/-- The object property on `Over (CommAlgCat.of A B)` of having a polynomial `A`-algebra as
source. -/
abbrev isPolynomialOver (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ObjectProperty (Over (CommAlgCat.of A B)) :=
  fun X ↦ IsPolynomial A X.left

/-- Unfolding `isPolynomialOver` recovers the polynomial-source property. -/
theorem isPolynomialOver_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (X : Over (CommAlgCat.of A B)) :
    isPolynomialOver A B X ↔ IsPolynomial A X.left :=
  sorry

/-- The category of `A`-algebra maps `P ⟶ B` with `P` a polynomial algebra over `A`. -/
abbrev PolynomialOver (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  (isPolynomialOver A B).FullSubcategory

/-- The opposite of the category of polynomial `A`-algebra maps to `B`. This is the site
`C_{B/A}` of Stacks tag 08PS, equipped in later use with the chaotic topology `⊥`. -/
abbrev PolynomialSite (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  (PolynomialOver A B)ᵒᵖ

namespace PolynomialOver

/-- The polynomial object `A[σ] ⟶ B` associated to a generating map `σ → B`. -/
noncomputable def ofGenerators (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {σ : Type u} (f : σ → B) : PolynomialOver A B where
  obj := Over.mk (CommAlgCat.ofHom (MvPolynomial.aeval f))
  property := MvPolynomial.instIsPolynomial

/-- The underlying arrow of `ofGenerators A f` is evaluation of polynomials at `f`. -/
theorem ofGenerators_obj (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {σ : Type u} (f : σ → B) :
    (ofGenerators A f).obj = Over.mk (CommAlgCat.ofHom (MvPolynomial.aeval f)) :=
  sorry

/-- Membership in `PolynomialOver A B` is the polynomial-source property on the over
category of `B`. -/
theorem mem_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (X : Over (CommAlgCat.of A B)) :
    IsPolynomial A X.left ↔ ∃ Y : PolynomialOver A B, Y.obj = X :=
  sorry

/-- Every polynomial algebra map to `B` factors in the over category through a polynomial
algebra on a generating set of cardinality at most that of `B`, as a retraction. This records
the source footnote without shrinking the objects of `PolynomialOver`. -/
theorem exists_generating_set_cardinal_le {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {σ : Type u} (f : σ → B) :
    ∃ (ι : Type u) (g : ι → B)
      (r : (ofGenerators A f).obj ⟶ (ofGenerators A g).obj)
      (s : (ofGenerators A g).obj ⟶ (ofGenerators A f).obj),
      Cardinal.mk ι ≤ Cardinal.mk B ∧ s ≫ r = 𝟙 (ofGenerators A g).obj :=
  sorry

end PolynomialOver

namespace PolynomialSite

/-- The underlying source of an object of `PolynomialSite A B` is a polynomial `A`-algebra. -/
theorem unop_isPolynomial {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (X : PolynomialSite A B) :
    IsPolynomial A X.unop.obj.left :=
  sorry

end PolynomialSite

end Algebra
