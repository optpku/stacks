module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension

/-!
# Schlessinger's (S1) along small extensions

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (S1)
as soon as the diagram-completion condition of Definition 90.10.1 holds along
small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.10.2: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
then `p` satisfies (S1) as soon as the diagram-completion condition of
`HasSchlessingerS1` is assumed only along morphisms `A₂ ⟶ A` that are small
extensions. Informally, every cospan in `F` lying over `A₁ ⟶ A ← A₂` with
`A₂ ⟶ A` a small extension completes to a commutative square lying over a
fibre product `A₁ ×_A A₂`. -/
@[stacks 06HX]
theorem hasSchlessingerS1_of_exists_completion_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (h : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      IsSmallExtension (p.map f2) →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)) :
    HasSchlessingerS1 p := sorry

/-- For a functor cofibered in groupoids, Schlessinger's condition (S1) is
equivalent to existence of a commutative completion whose image square is a
pullback, along a small extension. -/
theorem hasSchlessingerS1_iff_exists_completion_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    HasSchlessingerS1 p ↔
      ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
        IsSmallExtension (p.map f2) →
          ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
            CommSq π1 π2 f1 f2 ∧
              IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- The (S1) diagram-completion condition specializes along small extensions. -/
theorem HasSchlessingerS1.exists_completion_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasSchlessingerS1 p]
    {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x)
    (hf2 : IsSmallExtension (p.map f2)) :
    ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
      CommSq π1 π2 f1 f2 ∧
        IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

end CategoryTheory.Functor
