module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Factorization

/-!
# Schlessinger's condition (S1) along small extensions

For a category cofibered in groupoids over Artinian local algebras, the
diagram-completion condition along small extensions implies the full condition (S1).
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor cofibered in groupoids over Artinian local algebras satisfies
Schlessinger's condition (S1) if every cospan whose second base leg is a small
extension admits a commutative completion lying over a pullback. -/
theorem hasSchlessingerS1_of_exists_completion_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (h : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      IsSmallExtension (p.map f2) →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)) :
    HasSchlessingerS1 p := sorry

end CategoryTheory.Functor
