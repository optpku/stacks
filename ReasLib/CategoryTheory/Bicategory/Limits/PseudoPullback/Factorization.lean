/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Factor the right edge f ≫ g of a 2-commutative square, retaining the right-hand square

                         sq.snd ≫ f
                 sq.pt ─────────────────────────▶ Y
                    │                              │
             sq.fst │                              │ g
                    ▼                              ▼
                    T ───────────────────────────▶ Z
                                  z

and absorbing the associator into its comparison isomorphism. -/
def factorRight (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    Bicategory.PseudoPullbackCone z g where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd ≫ f
  iso := sq.iso ≪≫ (α_ sq.snd f g).symm

/-- Factoring the right edge of a pseudopullback cone leaves its apex unchanged. -/
@[simp]
theorem factorRight.pt (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).pt = sq.pt := sorry

/-- Factoring the right edge of a pseudopullback cone leaves its first projection unchanged. -/
@[simp]
theorem factorRight.fst (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).fst = sq.fst := sorry

/-- Factoring the right edge of a pseudopullback cone composes its second projection with the
first factor. -/
@[simp]
theorem factorRight.snd (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).snd = sq.snd ≫ f := sorry

/-- The comparison of a right-factorized pseudopullback cone is the original comparison
followed by the inverse associator. -/
@[simp]
theorem factorRight.iso (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).iso = sq.iso ≪≫ (α_ sq.snd f g).symm := sorry

/-- The forward comparison cell of a right-factorized pseudopullback cone is the original
forward cell followed by the inverse associator cell. -/
@[simp]
theorem factorRight.iso.hom (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).iso.hom = sq.iso.hom ≫ (α_ sq.snd f g).inv := sorry

/-- The inverse comparison cell of a right-factorized pseudopullback cone is the associator
cell followed by the original inverse comparison cell. -/
@[simp]
theorem factorRight.iso.inv (sq : Bicategory.PseudoPullbackCone z (f ≫ g)) :
    (factorRight sq).iso.inv = (α_ sq.snd f g).hom ≫ sq.iso.inv := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
