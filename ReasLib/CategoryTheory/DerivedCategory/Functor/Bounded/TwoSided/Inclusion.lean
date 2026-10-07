module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Basic

/-!
# Inclusion comparison for the two-sided bounded induced functor

After inclusion into the unbounded derived category, the bounded induced functor agrees with the
restriction of the unbounded induced functor.  Component lemmas expose the comparison without
unfolding its associators and whiskerings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.toBoundedDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

/-- After including `Dᵇ(ℬ)` in `D(ℬ)`, the bounded functor induced by `F` agrees with
the restriction of the unbounded induced functor. -/
@[stacks 05T4]
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedDerived ⋙ DerivedCategory.Bounded.ι ≅
      (HomotopyCategory.bounded 𝒜).ι ⋙ Functor.Homotopy.toDerived F :=
  (Functor.associator F.mapHomotopyCategoryBounded (DerivedCategory.Bounded.Qh ℬ)
      DerivedCategory.Bounded.ι).symm ≪≫
    Functor.isoWhiskerLeft F.mapHomotopyCategoryBounded
      (DerivedCategory.Bounded.Qh.compInclusionIso ℬ) ≪≫
    Functor.associator F.mapHomotopyCategoryBounded (HomotopyCategory.bounded ℬ).ι
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.Homotopy.Bounded.compInclusionIso F) DerivedCategory.Qh

namespace compInclusionIso

/-- The forward component of the bounded inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded derived inclusion computation"]
theorem hom_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Bounded 𝒜) :
    (toBoundedDerived.compInclusionIso F).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the bounded inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded derived inclusion computation"]
theorem inv_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Bounded 𝒜) :
    (toBoundedDerived.compInclusionIso F).inv.app X = 𝟙 _ := sorry

/-- Naturality of the forward bounded inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded derived inclusion computation"]
theorem hom_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Bounded 𝒜} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map (F.toBoundedDerived.map f) ≫
        (toBoundedDerived.compInclusionIso F).hom.app Y =
      (toBoundedDerived.compInclusionIso F).hom.app X ≫
        (Functor.Homotopy.toDerived F).map ((HomotopyCategory.bounded 𝒜).ι.map f) := sorry

/-- Naturality of the inverse bounded inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded derived inclusion computation"]
theorem inv_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Bounded 𝒜} (f : X ⟶ Y) :
    (Functor.Homotopy.toDerived F).map ((HomotopyCategory.bounded 𝒜).ι.map f) ≫
        (toBoundedDerived.compInclusionIso F).inv.app Y =
      (toBoundedDerived.compInclusionIso F).inv.app X ≫
        DerivedCategory.Bounded.ι.map (F.toBoundedDerived.map f) := sorry

end compInclusionIso


end CategoryTheory.Functor.toBoundedDerived
