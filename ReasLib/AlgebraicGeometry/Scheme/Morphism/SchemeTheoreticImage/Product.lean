/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Products of scheme-theoretic images

This file packages canonical scheme-theoretic image factorizations in an over category and
relates them to products over a field.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S : Scheme.{u}} {A X B Y : Over S}

/-- The scheme-theoretic image of an over-category morphism, equipped with its induced
structure morphism to the base. -/
noncomputable def imageOver (f : A ⟶ X) : Over S :=
  Over.mk (f.left.imageι ≫ X.hom)

/-- The canonical morphism from the source of an over-category morphism to its
scheme-theoretic image over the base. -/
noncomputable def toImageOver (f : A ⟶ X) : A ⟶ imageOver f :=
  Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ X.hom) = A.hom
    rw [← Category.assoc, f.left.toImage_imageι]
    exact f.w)

/-- The canonical closed-immersion leg from the scheme-theoretic image of an over-category
morphism to its target over the base. -/
noncomputable def imageιOver (f : A ⟶ X) : imageOver f ⟶ X :=
  Over.homMk f.left.imageι (by rfl)

/-- The underlying morphism of the canonical image inclusion over a base is a closed
immersion. -/
instance imageιOver_isClosedImmersion (f : A ⟶ X) :
    IsClosedImmersion (imageιOver f).left :=
  inferInstanceAs (IsClosedImmersion f.left.imageι)

/-- Over a field, the product of the canonical scheme-theoretic image factorizations of two
quasi-compact morphisms is a scheme-theoretic image factorization of their product. -/
theorem isSchemeTheoreticImageFactorization_tensor_overField
    {k : Type u} [Field k]
    {A X B Y : Over (Spec (CommRingCat.of k))}
    (f : A ⟶ X) (g : B ⟶ Y)
    [QuasiCompact f.left] [QuasiCompact g.left] :
    IsSchemeTheoreticImageFactorization ((f ⊗ₘ g).left)
      ((toImageOver f ⊗ₘ toImageOver g).left)
      ((imageιOver f ⊗ₘ imageιOver g).left) := sorry

end AlgebraicGeometry.Scheme.Hom
