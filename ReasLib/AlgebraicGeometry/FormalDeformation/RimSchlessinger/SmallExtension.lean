module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Rim-Schlessinger along small extensions

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies the
Rim-Schlessinger condition if projected pullbacks exist along small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor cofibered in groupoids satisfies the Rim-Schlessinger condition if
every cospan whose second projected morphism is a small extension admits a
pullback whose projected square is also a pullback. -/
@[stacks 06J4]
theorem hasRimSchlessinger_of_exists_pullback_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (h : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      IsSmallExtension (p.map f2) →
        ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
          IsPullback π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)) :
    HasRimSchlessinger p := sorry

/-- For a functor cofibered in groupoids, the Rim-Schlessinger condition is
equivalent to existence of fibre products lying over ring-level fibre products
along a small extension. -/
theorem hasRimSchlessinger_iff_exists_pullback_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    HasRimSchlessinger p ↔
      ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
        IsSmallExtension (p.map f2) →
          ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
            IsPullback π1 π2 f1 f2 ∧
              IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- The Rim-Schlessinger fibre-product condition specializes along small
extensions. -/
theorem HasRimSchlessinger.exists_pullback_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x)
    (hf2 : IsSmallExtension (p.map f2)) :
    ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
      IsPullback π1 π2 f1 f2 ∧
        IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

end CategoryTheory.Functor
