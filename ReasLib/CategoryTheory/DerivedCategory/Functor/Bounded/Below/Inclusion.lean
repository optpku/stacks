module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic

/-!
# Inclusion comparison for the bounded-below induced functor

@stack 05T4

After inclusion into the unbounded derived category, the bounded-below induced functor agrees
with the restriction of the unbounded induced functor.  The component API makes that comparison
usable without unfolding its associators and whiskerings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.toBoundedBelowDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

/-- After including `D⁺(ℬ)` in `D(ℬ)`, the bounded-below functor induced by `F` agrees with
the restriction of the unbounded induced functor. -/
@[stacks 05T4]
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedBelowDerived ⋙ DerivedCategory.Plus.ι ≅
      (HomotopyCategory.plus 𝒜).ι ⋙ Functor.Homotopy.toDerived F :=
  (Functor.associator F.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh
      DerivedCategory.Plus.ι).symm ≪≫
    Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
      (DerivedCategory.Plus.QhCompιIsoιCompQh ℬ) ≪≫
    Functor.associator F.mapHomotopyCategoryPlus (HomotopyCategory.plus ℬ).ι
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.Homotopy.Plus.compInclusionIso F) DerivedCategory.Qh

namespace compInclusionIso

/-- The forward component of the bounded-below inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded-below derived inclusion computation"]
theorem hom_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Plus 𝒜) :
    (toBoundedBelowDerived.compInclusionIso F).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the bounded-below inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded-below derived inclusion computation"]
theorem inv_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Plus 𝒜) :
    (toBoundedBelowDerived.compInclusionIso F).inv.app X = 𝟙 _ := sorry

/-- Naturality of the forward bounded-below inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded-below derived inclusion computation"]
theorem hom_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Plus 𝒜} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map (F.toBoundedBelowDerived.map f) ≫
        (toBoundedBelowDerived.compInclusionIso F).hom.app Y =
      (toBoundedBelowDerived.compInclusionIso F).hom.app X ≫
        (Functor.Homotopy.toDerived F).map ((HomotopyCategory.plus 𝒜).ι.map f) := sorry

/-- Naturality of the inverse bounded-below inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded-below derived inclusion computation"]
theorem inv_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Plus 𝒜} (f : X ⟶ Y) :
    (Functor.Homotopy.toDerived F).map ((HomotopyCategory.plus 𝒜).ι.map f) ≫
        (toBoundedBelowDerived.compInclusionIso F).inv.app Y =
      (toBoundedBelowDerived.compInclusionIso F).inv.app X ≫
        DerivedCategory.Plus.ι.map (F.toBoundedBelowDerived.map f) := sorry

end compInclusionIso


end CategoryTheory.Functor.toBoundedBelowDerived
