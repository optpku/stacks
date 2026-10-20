/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite

/-!
# Polynomial commutative algebras over a target

Polynomial augmentations use the unrestricted category `Algebra.PolynomialOver`.
The cardinality bound on generating sets does not restrict its objects.
-/

@[expose] public section

open CategoryTheory

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

#check (Algebra.isPolynomialOver A B : ObjectProperty (Over (CommAlgCat.of A B)))
#check (Algebra.PolynomialOver A B : Type (u + 1))
#check (Algebra.isPolynomialOver_iff : ∀ (X : Over (CommAlgCat.of A B)),
  Algebra.isPolynomialOver A B X ↔ Algebra.IsPolynomial A X.left)
#check (CommAlgCat.Over.Polynomial.ofMvPolynomial A B :
  (ι : Type u) → (MvPolynomial ι A →ₐ[A] B) → Algebra.PolynomialOver A B)
#check (CommAlgCat.Over.Polynomial.ofMvPolynomial_obj A B :
  ∀ (ι : Type u) (aug : MvPolynomial ι A →ₐ[A] B),
    (CommAlgCat.Over.Polynomial.ofMvPolynomial A B ι aug).obj =
      Over.mk (CommAlgCat.ofHom aug))
#check (Algebra.PolynomialOver.exists_generating_set_cardinal_le :
  ∀ {σ : Type u} (f : σ → B),
    ∃ (ι : Type u) (g : ι → B)
      (r : (Algebra.PolynomialOver.ofGenerators A f).obj ⟶
        (Algebra.PolynomialOver.ofGenerators A g).obj)
      (s : (Algebra.PolynomialOver.ofGenerators A g).obj ⟶
        (Algebra.PolynomialOver.ofGenerators A f).obj),
      Cardinal.mk ι ≤ Cardinal.mk B ∧
        s ≫ r = 𝟙 (Algebra.PolynomialOver.ofGenerators A g).obj)
