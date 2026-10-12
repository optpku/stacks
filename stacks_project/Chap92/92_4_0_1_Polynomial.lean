/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver

/-!
# Polynomial commutative algebras over a target

This leaf identifies the category of polynomial `A`-algebras over `B` with the unrestricted
owner `Algebra.PolynomialOver`, and the site `C_{B/A}` with `Algebra.PolynomialSite`.  Sets of
cardinality at most that of `B` suffice cofinally, but they do not restrict membership.
-/

@[expose] public section

open CategoryTheory
universe u

noncomputable section

namespace CommAlgCat.Over.Polynomial

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The object property on `Over (CommAlgCat.of A B)` selecting polynomial `A`-algebras. -/
abbrev property : ObjectProperty (Over (CommAlgCat.of A B)) :=
  Algebra.isPolynomialOver A B

/-- The category of polynomial `A`-algebras equipped with a map to the target `A`-algebra `B`. -/
abbrev category := Algebra.PolynomialOver A B

/-- Membership in `property A B` is the polynomial-source property on the over-category of `B`. -/
theorem property_iff (P : Over (CommAlgCat.of A B)) :
    property A B P ↔ Algebra.IsPolynomial A P.left :=
  sorry

/-- A polynomial `A`-algebra over `B` presented by an explicit variable type `ι` and an
augmentation `MvPolynomial ι A →ₐ[A] B`. -/
def ofMvPolynomial (ι : Type u) (aug : MvPolynomial ι A →ₐ[A] B) : category A B where
  obj := Over.mk (CommAlgCat.ofHom aug)
  property := MvPolynomial.instIsPolynomial

/-- The underlying over-object of `ofMvPolynomial` is the augmentation `aug`. -/
theorem ofMvPolynomial_obj (ι : Type u) (aug : MvPolynomial ι A →ₐ[A] B) :
    (ofMvPolynomial A B ι aug).obj = Over.mk (CommAlgCat.ofHom aug) :=
  sorry

/-- Sets of cardinality at most that of `B` suffice cofinally among polynomial presentations
over `B`. This records the source footnote without shrinking the objects of `category`. -/
theorem exists_generating_set_cardinal_le {σ : Type u} (f : σ → B) :
    ∃ (ι : Type u) (g : ι → B)
      (r : (Algebra.PolynomialOver.ofGenerators A f).obj ⟶
          (Algebra.PolynomialOver.ofGenerators A g).obj)
      (s : (Algebra.PolynomialOver.ofGenerators A g).obj ⟶
          (Algebra.PolynomialOver.ofGenerators A f).obj),
      Cardinal.mk ι ≤ Cardinal.mk B ∧
        s ≫ r = 𝟙 (Algebra.PolynomialOver.ofGenerators A g).obj :=
  sorry

end CommAlgCat.Over.Polynomial
