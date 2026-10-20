module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Preadditive.Left

/-!
# Linear Naturality of Total Left-Derived Functors

Scalar multiplication of natural transformations is preserved by total left derivation when
the target category is linear. Linearity of the source functors and localization functor is
not required.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory.Functor.LeftDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
variable {R : Type w} [Semiring R] [Preadditive E] [CategoryTheory.Linear R E]

/-- Total left-derived maps preserve scalar multiplication of source natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.smul
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E}
    (r : R) (τ : F ⟶ G) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    mapNatTrans L S (r • τ) = r • mapNatTrans L S τ := sorry

end CategoryTheory.Functor.LeftDerived
