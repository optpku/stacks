/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor

@[expose] public section

/-!
# Naturality of the bounded quotient comparison

The comparison between termwise mapping before and after passage to the bounded homotopy
category is compatible with natural transformations.  Both the natural-transformation
equality and its pointwise form are provided for downstream rewriting.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Bounded

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The forward bounded quotient comparison is natural in the additive functor. -/
@[stacks 014X "naturality of the bounded quotient comparison"]
theorem quotientIso_hom_naturality (α : F ⟶ G) :
    (quotientIso F).hom ≫
        Functor.whiskerLeft (HomotopyCategory.Bounded.quotient C) (natTrans α) =
      Functor.whiskerRight (Functor.Cochain.Bounded.natTrans α)
          (HomotopyCategory.Bounded.quotient D) ≫
        (quotientIso G).hom := sorry

/-- Pointwise form of naturality for the forward bounded quotient comparison. -/
theorem quotientIso_hom_naturality_app (α : F ⟶ G) (K : CochainComplex.Bounded C) :
    (quotientIso F).hom.app K ≫
        (natTrans α).app ((HomotopyCategory.Bounded.quotient C).obj K) =
      (HomotopyCategory.Bounded.quotient D).map
          ((Functor.Cochain.Bounded.natTrans α).app K) ≫
        (quotientIso G).hom.app K := sorry

/-- The inverse bounded quotient comparison is natural in the additive functor. -/
theorem quotientIso_inv_naturality (α : F ⟶ G) :
    Functor.whiskerLeft (HomotopyCategory.Bounded.quotient C) (natTrans α) ≫
        (quotientIso G).inv =
      (quotientIso F).inv ≫
        Functor.whiskerRight (Functor.Cochain.Bounded.natTrans α)
          (HomotopyCategory.Bounded.quotient D) := sorry

/-- Pointwise form of naturality for the inverse bounded quotient comparison. -/
theorem quotientIso_inv_naturality_app (α : F ⟶ G) (K : CochainComplex.Bounded C) :
    (natTrans α).app ((HomotopyCategory.Bounded.quotient C).obj K) ≫
        (quotientIso G).inv.app K =
      (quotientIso F).inv.app K ≫
        (HomotopyCategory.Bounded.quotient D).map
          ((Functor.Cochain.Bounded.natTrans α).app K) := sorry

end CategoryTheory.Functor.Homotopy.Bounded
