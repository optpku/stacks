/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.FullyFaithful

@[expose] public section

/-!
# K-Projective Computation of Pointwise Left Derived Values

This leaf turns the K-projective hom-lifting theorem into sourcewise full faithfulness of the
canonical quasi-isomorphism localization. The neutral endpoint API then supplies the initial
identity denominator and the pointwise left-derived computation criterion.
-/

open CategoryTheory Limits ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KProjective

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [Category.{v₂} 𝒟']

/-- Stacks 064B: localization at quasi-isomorphisms is bijective on morphisms from the image of
a K-projective cochain complex. -/
@[stacks 064B]
theorem Localization.map_bijective
    (P : CochainComplex 𝒜 ℤ) (L : HomotopyCategory 𝒜 (up ℤ)) [P.IsKProjective] :
    Function.Bijective
      ((MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶ L) →
          ((MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).obj
              ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P) ⟶
            (MorphismProperty.Q (HomotopyCategory.quasiIso 𝒜 (up ℤ))).obj L)) := sorry

/-- Stacks 064B: a K-projective cochain complex computes the pointwise left-derived value of
every functor out of the homotopy category, with respect to quasi-isomorphisms. -/
@[stacks 064B]
noncomputable instance computesAt
    (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟') (P : CochainComplex 𝒜 ℤ) [P.IsKProjective] :
    LeftDerived.ComputesAt F (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P) := sorry

end CategoryTheory.Functor.KProjective
