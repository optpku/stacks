module

public import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.FullyFaithful

@[expose] public section

/-!
# K-Injective Computation of Pointwise Right Derived Values

This leaf turns the K-injective hom-lifting theorem into targetwise full faithfulness of the
canonical quasi-isomorphism localization.  The neutral endpoint API then supplies the terminal
identity denominator and the pointwise right-derived computation criterion.
-/

open CategoryTheory Limits ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KInjective

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [Category.{v₂} 𝒟']

/-- Stacks 070Y: localization at quasi-isomorphisms is bijective on morphisms into the image of
a K-injective cochain complex. -/
@[stacks 070Y]
theorem Localization.map_bijective
    (K : HomotopyCategory 𝒜 (up ℤ)) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    Function.Bijective
      ((MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).map :
        (K ⟶ (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I) →
          ((MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).obj K ⟶
            (MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).obj
              ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj I))) := sorry

/-- Stacks 070Y: a K-injective cochain complex computes the pointwise right-derived value of
every functor out of the homotopy category, with respect to quasi-isomorphisms. -/
@[stacks 070Y]
noncomputable instance computesAt
    (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟') (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    RightDerived.ComputesAt F (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj I) := sorry



end CategoryTheory.Functor.KInjective
