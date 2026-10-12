/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_6_7_Instances
public import stacks_project.Chap71.Lemma_71_7_3_AssociatedSheaf

/-!
# Lemma 71.7.3

The associated sheaf of a sum of effective Cartier divisors on an algebraic
space is the tensor product of the associated sheaves, uniquely so among
isomorphisms sending 1_{D₁} ⊗ 1_{D₂} to 1_D.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- An isomorphism `associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅ associatedSheaf (D₁ + D₂)`
is compatible when it sends 1_{D₁} ⊗ 1_{D₂} to 1_D. -/
abbrev IsAssociatedSheafSumIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂)) : Prop :=
  (λ_ (𝟙_ X.Modules)).inv ≫
      (canonicalSectionHom D₁ ⊗ₘ canonicalSectionHom D₂) ≫ e.hom =
    canonicalSectionHom (effectiveCartierDivisorSum D₁ D₂)

/-- Compatibility of a sum isomorphism with canonical sections is the identity of
the corresponding unit morphisms. -/
theorem isAssociatedSheafSumIso_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂)) :
    IsAssociatedSheafSumIso D₁ D₂ e ↔
      (λ_ (𝟙_ X.Modules)).inv ≫
          (canonicalSectionHom D₁ ⊗ₘ canonicalSectionHom D₂) ≫ e.hom =
        canonicalSectionHom (effectiveCartierDivisorSum D₁ D₂) :=
  sorry

/-- Lemma 71.7.3. Let `S` be a scheme and let `X` be an algebraic space over `S`.
Let `D₁`, `D₂` be effective Cartier divisors on `X`, and write
`D = effectiveCartierDivisorSum D₁ D₂`. Then there is a unique isomorphism
`associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅ associatedSheaf D` sending
`1_{D₁} ⊗ 1_{D₂}` to `1_D`. -/
@[stacks 0842]
theorem existsUnique_associatedSheafSumIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    ∃! e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂),
      IsAssociatedSheafSumIso D₁ D₂ e :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
