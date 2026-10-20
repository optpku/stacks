module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Cofibered.PushforwardComparison
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Categorical comparisons for the Rim-Schlessinger condition

The Rim-Schlessinger condition is equivalent to equivalence of the canonical
fibre-category comparison functors along surjections, or along small extensions.
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

/-- For a category cofibered in groupoids, the Rim-Schlessinger condition is
equivalent to equivalence of the canonical fibre-category comparison along every
pullback square with surjective second leg, and equivalently with second leg a
small extension. -/
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

/-- The Rim-Schlessinger condition is equivalent to the canonical fibre-category
comparison being an equivalence along every pullback square with a surjective
second leg. -/
theorem hasRimSchlessinger_iff_fiberComparison_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger p ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        Function.Surjective f2.hom → (fiberComparison p χ h.w).IsEquivalence :=
  sorry

/-- The Rim-Schlessinger condition is equivalent to the canonical fibre-category
comparison being an equivalence along every pullback square whose second leg is
a small extension. -/
theorem hasRimSchlessinger_iff_fiberComparison_isEquivalence_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger p ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        IsSmallExtension f2 → (fiberComparison p χ h.w).IsEquivalence :=
  sorry

/-- Under the Rim-Schlessinger condition, the canonical fibre-category comparison
is an equivalence along every pullback square with a surjective second leg. -/
theorem HasRimSchlessinger.fiberComparison_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (χ : p.op.Cleavage)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2)
    (hf2 : Function.Surjective f2.hom) :
    (fiberComparison p χ h.w).IsEquivalence :=
  sorry

/-- Fact-certified pullback and surjectivity hypotheses make the canonical
fibre-category comparison an equivalence under the Rim-Schlessinger condition. -/
instance HasRimSchlessinger.instIsEquivalenceFiberComparison
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (χ : p.op.Cleavage)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (hw : π1 ≫ f1 = π2 ≫ f2)
    [Fact (IsPullback π1 π2 f1 f2)] [Fact (Function.Surjective f2.hom)] :
    (fiberComparison p χ hw).IsEquivalence :=
  HasRimSchlessinger.fiberComparison_isEquivalence p χ f1 f2 π1 π2
    (Fact.out : IsPullback π1 π2 f1 f2) (Fact.out : Function.Surjective f2.hom)

end CategoryTheory.Functor
