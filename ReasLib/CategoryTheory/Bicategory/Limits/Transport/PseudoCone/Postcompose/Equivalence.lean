/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.Biequivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Constructors

/-!
# Postcomposition by pointwise equivalences

Postcomposition by a strong transformation equipped with pointwise equivalence data is a
biequivalence between the corresponding bicategories of conical pseudocones. Consequently,
it preserves and reflects the bilimit property.

The pointwise formulation is the primary API. A functor-bicategory equivalence supplies
that data canonically and is exposed only as a convenient specialization.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E F : Pseudofunctor J B}

/-- Postcomposition by a pointwise-equivalence strong transformation is a
biequivalence of bicategories of conical pseudocones. -/
theorem postcompose_isBiequivalence
    (α : Pseudofunctor.StrongTrans E F)
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence α) :
    Pseudofunctor.IsBiequivalence (postcompose α) := sorry

/-- Postcomposition by the forward transformation of a functor-bicategory equivalence is
a biequivalence of bicategories of conical pseudocones. -/
instance postcomposeIsBiequivalence
    (e : E ≌ F) :
    Pseudofunctor.IsBiequivalence (postcompose e.hom) := sorry

/-- Postcomposition by a pointwise equivalence preserves the bilimit property. -/
theorem postcomposeObj_isBilimit
    (α : Pseudofunctor.StrongTrans E F)
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence α)
    (S : PseudoCone E) [S.IsBilimit] :
    (postcomposeObj α S).IsBilimit := sorry

/-- Postcomposition by a pointwise equivalence reflects the bilimit property. -/
theorem isBilimit_of_postcomposeObj
    (α : Pseudofunctor.StrongTrans E F)
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence α)
    (S : PseudoCone E) [(postcomposeObj α S).IsBilimit] :
    S.IsBilimit := sorry

/-- Postcomposition by a pointwise equivalence preserves and reflects the bilimit
property. -/
theorem postcomposeObj_isBilimit_iff
    (α : Pseudofunctor.StrongTrans E F)
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence α)
    (S : PseudoCone E) :
    (postcomposeObj α S).IsBilimit ↔ S.IsBilimit := sorry

/-- Postcomposition by the forward transformation of a functor-bicategory equivalence
preserves and reflects the bilimit property. -/
theorem postcomposeObj_isBilimit_iff_of_equivalence
    (e : E ≌ F) (S : PseudoCone E) :
    (postcomposeObj e.hom S).IsBilimit ↔ S.IsBilimit := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces only `Prop`-valued consequences. The supplied
`PointwiseEquivalence` remains the canonical owner of all inverse, unit, and counit data;
no second pseudoinverse or component equivalence is selected here. -/

end Bicategory.PseudoCone

end CategoryTheory
