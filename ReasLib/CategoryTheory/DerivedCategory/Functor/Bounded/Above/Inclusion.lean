/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic

/-!
# Inclusion comparison for the bounded-above induced functor

@stack 05T4

After inclusion into the unbounded derived category, the bounded-above induced functor agrees
with the restriction of the unbounded induced functor.  Component lemmas expose the comparison
without unfolding its associators and whiskerings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.toBoundedAboveDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

/-- After including `D⁻(ℬ)` in `D(ℬ)`, the bounded-above functor induced by `F` agrees with
the restriction of the unbounded induced functor. -/
@[stacks 05T4]
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedAboveDerived ⋙ DerivedCategory.Minus.ι ≅
      (HomotopyCategory.minus 𝒜).ι ⋙ Functor.Homotopy.toDerived F :=
  (Functor.associator F.mapHomotopyCategoryMinus (DerivedCategory.Minus.Qh ℬ)
      DerivedCategory.Minus.ι).symm ≪≫
    Functor.isoWhiskerLeft F.mapHomotopyCategoryMinus
      (DerivedCategory.Minus.Qh.compInclusionIso ℬ) ≪≫
    Functor.associator F.mapHomotopyCategoryMinus (HomotopyCategory.minus ℬ).ι
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.Homotopy.Minus.compInclusionIso F) DerivedCategory.Qh

namespace compInclusionIso

/-- The forward component of the bounded-above inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded-above derived inclusion computation"]
theorem hom_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Minus 𝒜) :
    (toBoundedAboveDerived.compInclusionIso F).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the bounded-above inclusion comparison is identity. -/
@[simp, stacks 05T4 "bounded-above derived inclusion computation"]
theorem inv_app (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Minus 𝒜) :
    (toBoundedAboveDerived.compInclusionIso F).inv.app X = 𝟙 _ := sorry

/-- Naturality of the forward bounded-above inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded-above derived inclusion computation"]
theorem hom_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Minus 𝒜} (f : X ⟶ Y) :
    DerivedCategory.Minus.ι.map (F.toBoundedAboveDerived.map f) ≫
        (toBoundedAboveDerived.compInclusionIso F).hom.app Y =
      (toBoundedAboveDerived.compInclusionIso F).hom.app X ≫
        (Functor.Homotopy.toDerived F).map ((HomotopyCategory.minus 𝒜).ι.map f) := sorry

/-- Naturality of the inverse bounded-above inclusion comparison in component form. -/
@[reassoc (attr := simp), stacks 05T4 "bounded-above derived inclusion computation"]
theorem inv_naturality (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Minus 𝒜} (f : X ⟶ Y) :
    (Functor.Homotopy.toDerived F).map ((HomotopyCategory.minus 𝒜).ι.map f) ≫
        (toBoundedAboveDerived.compInclusionIso F).inv.app Y =
      (toBoundedAboveDerived.compInclusionIso F).inv.app X ≫
        DerivedCategory.Minus.ι.map (F.toBoundedAboveDerived.map f) := sorry

end compInclusionIso


end CategoryTheory.Functor.toBoundedAboveDerived
