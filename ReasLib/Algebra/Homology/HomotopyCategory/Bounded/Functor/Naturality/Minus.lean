/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor

@[expose] public section

/-!
# Naturality of the bounded-above quotient comparison

The comparison between termwise mapping before and after passage to the bounded-above
homotopy category is compatible with natural transformations.  Both the natural-
transformation equality and its pointwise form are provided for downstream rewriting.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Minus

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The forward bounded-above quotient comparison is natural in the additive functor. -/
@[stacks 014X "naturality of the bounded-above quotient comparison"]
theorem quotientIso_hom_naturality (α : F ⟶ G) :
    (quotientIso F).hom ≫
        Functor.whiskerLeft (HomotopyCategory.Minus.quotient C) (natTrans α) =
      Functor.whiskerRight (Functor.Cochain.Minus.natTrans α)
          (HomotopyCategory.Minus.quotient D) ≫
        (quotientIso G).hom := sorry

/-- Pointwise form of naturality for the forward bounded-above quotient comparison. -/
theorem quotientIso_hom_naturality_app (α : F ⟶ G) (K : CochainComplex.Minus C) :
    (quotientIso F).hom.app K ≫
        (natTrans α).app ((HomotopyCategory.Minus.quotient C).obj K) =
      (HomotopyCategory.Minus.quotient D).map
          ((Functor.Cochain.Minus.natTrans α).app K) ≫
        (quotientIso G).hom.app K := sorry

/-- The inverse bounded-above quotient comparison is natural in the additive functor. -/
theorem quotientIso_inv_naturality (α : F ⟶ G) :
    Functor.whiskerLeft (HomotopyCategory.Minus.quotient C) (natTrans α) ≫
        (quotientIso G).inv =
      (quotientIso F).inv ≫
        Functor.whiskerRight (Functor.Cochain.Minus.natTrans α)
          (HomotopyCategory.Minus.quotient D) := sorry

/-- Pointwise form of naturality for the inverse bounded-above quotient comparison. -/
theorem quotientIso_inv_naturality_app (α : F ⟶ G) (K : CochainComplex.Minus C) :
    (natTrans α).app ((HomotopyCategory.Minus.quotient C).obj K) ≫
        (quotientIso G).inv.app K =
      (quotientIso F).inv.app K ≫
        (HomotopyCategory.Minus.quotient D).map
          ((Functor.Cochain.Minus.natTrans α).app K) := sorry

end CategoryTheory.Functor.Homotopy.Minus
