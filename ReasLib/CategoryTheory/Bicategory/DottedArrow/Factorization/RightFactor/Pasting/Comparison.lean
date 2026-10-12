/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Const
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Pasting.Basic

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (sq : Bicategory.PseudoPullbackCone z (f ≫ g))

section FactorPasteNatIsoImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Left-comparison compatibility for the canonical comparison from d to the refactored paste.

Proof strategy: this is the hom component of A.comm. -/
private theorem factorPasteHom_left_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    (Bicategory.PseudoPullbackCone.factorRight sq).fst ◁ A.right.hom ≫
        ((factorRightFunctor sq).obj ((pasteFunctor sq d).obj A)).left.hom =
      d.left.hom := sorry

/-- Right-comparison compatibility for the canonical comparison from d to the refactored paste.

Proof strategy: unfold the public computation API for factorRightFunctor and pasteFunctor, then
cancel the inserted associator. -/
private theorem factorPasteHom_right_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    d.right.hom ≫ A.right.hom ▷ g =
      ((factorRightFunctor sq).obj ((pasteFunctor sq d).obj A)).right.hom := sorry

/-- The canonical comparison from d to the middle factor of a pasted dotted arrow. -/
private def factorPasteHom
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    d ⟶ (factorRightFunctor sq).obj ((pasteFunctor sq d).obj A) where
  hom := A.right.hom
  left_comm := factorPasteHom_left_comm sq d A
  right_comm := factorPasteHom_right_comm sq d A

/-- Left-comparison compatibility for the inverse canonical comparison.

Proof strategy: compose factorPasteHom_left_comm with A.right.inv and cancel A.right.hom. -/
private theorem factorPasteInv_left_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    (Bicategory.PseudoPullbackCone.factorRight sq).fst ◁ A.right.inv ≫ d.left.hom =
      ((factorRightFunctor sq).obj ((pasteFunctor sq d).obj A)).left.hom := sorry

/-- Right-comparison compatibility for the inverse canonical comparison.

Proof strategy: compose factorPasteHom_right_comm with A.right.inv and cancel A.right.hom. -/
private theorem factorPasteInv_right_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((factorRightFunctor sq).obj ((pasteFunctor sq d).obj A)).right.hom ≫
        A.right.inv ▷ g =
      d.right.hom := sorry

/-- The explicit inverse of factorPasteHom. -/
private def factorPasteInv
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    (factorRightFunctor sq).obj ((pasteFunctor sq d).obj A) ⟶ d where
  hom := A.right.inv
  left_comm := factorPasteInv_left_comm sq d A
  right_comm := factorPasteInv_right_comm sq d A

/-- The forward and inverse factor-paste comparisons compose to the identity on d.

Proof strategy: apply DottedArrow.Hom.ext and use A.right.hom_inv_id. -/
private theorem factorPaste_hom_inv_id
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    factorPasteHom sq d A ≫ factorPasteInv sq d A = 𝟙 d := sorry

/-- The inverse and forward factor-paste comparisons compose to the identity on the refactored
pasted object.

Proof strategy: apply DottedArrow.Hom.ext and use A.right.inv_hom_id. -/
private theorem factorPaste_inv_hom_id
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    factorPasteInv sq d A ≫ factorPasteHom sq d A =
      𝟙 ((factorRightFunctor sq).obj ((pasteFunctor sq d).obj A)) := sorry

/-- The pointwise isomorphism underlying the natural factor-paste comparison. -/
private def factorPasteComponent
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    d ≅ (factorRightFunctor sq).obj ((pasteFunctor sq d).obj A) where
  hom := factorPasteHom sq d A
  inv := factorPasteInv sq d A
  hom_inv_id := factorPaste_hom_inv_id sq d A
  inv_hom_id := factorPaste_inv_hom_id sq d A

/-- Naturality of the pointwise factor-paste comparison.

Proof strategy: apply DottedArrow.Hom.ext; after the constant functor map is simplified, the
remaining equation is η.right_comm. -/
private theorem factorPasteComponent_naturality
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    ((Functor.const (DottedArrow (leftFactorSquare sq d))).obj d).map η ≫
        (factorPasteComponent sq d A').hom =
      (factorPasteComponent sq d A).hom ≫
        (pasteFunctor sq d ⋙ factorRightFunctor sq).map η := sorry

end Implementation

/-- Pasting and then taking the right factor is naturally isomorphic to the constant functor at
the fixed middle dotted arrow d. The component at A is induced by A.right. -/
def factorPasteNatIso
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (Functor.const (DottedArrow (leftFactorSquare sq d))).obj d ≅
      pasteFunctor sq d ⋙ factorRightFunctor sq :=
  NatIso.ofComponents (Implementation.factorPasteComponent sq d)
    (Implementation.factorPasteComponent_naturality sq d)

end FactorPasteNatIsoImplementation

/-- The ambient 2-morphism of a forward factor-paste component.

Proof strategy: unfold factorPasteNatIso and its private pointwise comparison. -/
@[simp] theorem factorPasteNatIso.app.hom
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((factorPasteNatIso sq d).hom.app A).hom = A.right.hom := sorry

/-- The ambient 2-morphism of an inverse factor-paste component.

Proof strategy: unfold factorPasteNatIso and its private pointwise comparison. -/
@[simp] theorem factorPasteNatIso.app.inv
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((factorPasteNatIso sq d).inv.app A).hom = A.right.inv := sorry

end DottedArrow

end CategoryTheory
