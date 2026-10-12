/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap90.«90_10_1_1_Comparison»
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension

/-!
# 2-categorical form of the Rim-Schlessinger condition

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS) if and
only if the fibre-category comparison of (90.10.1.1) is an equivalence along fibre
products whose second leg is surjective, and equivalently along small extensions.
-/

@[expose] public section

open CategoryTheory Functor Limits
open ArtinianLocalAlgCat (IsSmallExtension)
open scoped CategoricalPullback

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.16.4: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
then the following are equivalent: `p` satisfies (RS); the comparison functor
`fiberComparison p χ h.w` of (90.10.1.1) is an equivalence of categories whenever
`A₂ ⟶ A` is surjective; and the same comparison is an equivalence whenever
`A₂ ⟶ A` is a small extension. -/
@[stacks 06J5]
theorem hasRimSchlessinger_tfae
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    List.TFAE
      [HasRimSchlessinger p,
        ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
          (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
          Function.Surjective f2.hom → (fiberComparison p χ h.w).IsEquivalence,
        ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
          (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
          IsSmallExtension f2 → (fiberComparison p χ h.w).IsEquivalence] :=
  sorry

/-- The Rim-Schlessinger condition is equivalent to the fibre-category comparison of
(90.10.1.1) being an equivalence along every fibre-product square with a surjective
second leg. -/
theorem hasRimSchlessinger_iff_fiberComparison_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger p ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        Function.Surjective f2.hom → (fiberComparison p χ h.w).IsEquivalence :=
  sorry

/-- The Rim-Schlessinger condition is equivalent to the fibre-category comparison of
(90.10.1.1) being an equivalence along every fibre-product square whose second leg
is a small extension. -/
theorem hasRimSchlessinger_iff_fiberComparison_isEquivalence_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger p ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        IsSmallExtension f2 → (fiberComparison p χ h.w).IsEquivalence :=
  sorry

/-- Under (RS), the fibre-category comparison of (90.10.1.1) is an equivalence along
every fibre-product square with a surjective second leg. -/
theorem HasRimSchlessinger.fiberComparison_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (χ : p.op.Cleavage)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2)
    (hf2 : Function.Surjective f2.hom) :
    (fiberComparison p χ h.w).IsEquivalence :=
  sorry

end CategoryTheory.Functor
