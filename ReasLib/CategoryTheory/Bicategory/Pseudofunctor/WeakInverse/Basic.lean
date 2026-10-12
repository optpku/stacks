/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Biequivalence
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Weak inverses of pseudofunctors

Two pseudofunctors are weak inverses when both composites are equivalent to the corresponding
identity pseudofunctor. The equivalences are data: their strong transformations and invertible
modifications remain available to downstream bicategorical constructions.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- Chosen weak-inverse data for pseudofunctors `F : B ⥤ᵖ C` and `G : C ⥤ᵖ B`.
Each composite is equivalent, through strong transformations and invertible modifications, to
the identity pseudofunctor on its source. -/
structure WeakInverse (F : B ⥤ᵖ C) (G : C ⥤ᵖ B) where
  /-- The equivalence from `F` followed by `G` to the identity of `B`. -/
  left : F.comp G ≌ Pseudofunctor.id B
  /-- The equivalence from `G` followed by `F` to the identity of `C`. -/
  right : G.comp F ≌ Pseudofunctor.id C

namespace WeakInverse

variable {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}

/-- Exchanging the two pseudofunctors exchanges the two weak-inverse equivalences. -/
def symm (h : WeakInverse F G) : WeakInverse G F where
  left := h.right
  right := h.left

/-- The left pseudofunctor in a weak-inverse pair is a biequivalence. -/
theorem leftIsBiequivalence (h : WeakInverse F G) :
    F.IsBiequivalence := sorry

/-- The right pseudofunctor in a weak-inverse pair is a biequivalence. -/
theorem rightIsBiequivalence (h : WeakInverse F G) :
    G.IsBiequivalence := sorry

end WeakInverse

end CategoryTheory.Pseudofunctor
