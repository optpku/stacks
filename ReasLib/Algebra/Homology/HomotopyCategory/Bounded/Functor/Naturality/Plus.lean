module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor

@[expose] public section

/-!
# Naturality of the bounded-below quotient comparison

The comparison between termwise mapping before and after passage to the bounded-below
homotopy category is compatible with natural transformations.  Both the natural-
transformation equality and its pointwise form are provided for downstream rewriting.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Plus

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The forward bounded-below quotient comparison is natural in the additive functor. -/
@[stacks 014X "naturality of the bounded-below quotient comparison"]
theorem quotientIso_hom_naturality (α : F ⟶ G) :
    (quotientIso F).hom ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.quotient C) (natTrans α) =
      Functor.whiskerRight (Functor.Cochain.Plus.natTrans α)
          (HomotopyCategory.Plus.quotient D) ≫
        (quotientIso G).hom := sorry

/-- Pointwise form of naturality for the forward bounded-below quotient comparison. -/
theorem quotientIso_hom_naturality_app (α : F ⟶ G) (K : CochainComplex.Plus C) :
    (quotientIso F).hom.app K ≫
        (natTrans α).app ((HomotopyCategory.Plus.quotient C).obj K) =
      (HomotopyCategory.Plus.quotient D).map
          ((Functor.Cochain.Plus.natTrans α).app K) ≫
        (quotientIso G).hom.app K := sorry

/-- The inverse bounded-below quotient comparison is natural in the additive functor. -/
theorem quotientIso_inv_naturality (α : F ⟶ G) :
    Functor.whiskerLeft (HomotopyCategory.Plus.quotient C) (natTrans α) ≫
        (quotientIso G).inv =
      (quotientIso F).inv ≫
        Functor.whiskerRight (Functor.Cochain.Plus.natTrans α)
          (HomotopyCategory.Plus.quotient D) := sorry

/-- Pointwise form of naturality for the inverse bounded-below quotient comparison. -/
theorem quotientIso_inv_naturality_app (α : F ⟶ G) (K : CochainComplex.Plus C) :
    (natTrans α).app ((HomotopyCategory.Plus.quotient C).obj K) ≫
        (quotientIso G).inv.app K =
      (quotientIso F).inv.app K ≫
        (HomotopyCategory.Plus.quotient D).map
          ((Functor.Cochain.Plus.natTrans α).app K) := sorry

end CategoryTheory.Functor.Homotopy.Plus
