module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.SmallExtension
import StacksCheckRecall

/-!
# Rim-Schlessinger along small extensions

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS)
as soon as the fibre-product condition of Definition 90.16.1 holds along small
extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/- Lemma 90.16.3: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
then `p` satisfies (RS) as soon as the fibre-product condition of
`HasRimSchlessinger` is assumed only along morphisms `A₂ ⟶ A` that are small
extensions. -/
@[stacks 06J4]
#check (CategoryTheory.Functor.hasRimSchlessinger_of_exists_pullback_isSmallExtension :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (h : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      IsSmallExtension (p.map f2) →
        ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
          IsPullback π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)),
    HasRimSchlessinger p)

/- For a functor cofibered in groupoids, the Rim-Schlessinger condition is
equivalent to existence of fibre products lying over ring-level fibre products
along a small extension. -/
#check (CategoryTheory.Functor.hasRimSchlessinger_iff_exists_pullback_isSmallExtension :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    HasRimSchlessinger p ↔
      ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
        IsSmallExtension (p.map f2) →
          ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
            IsPullback π1 π2 f1 f2 ∧
              IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))

/- The Rim-Schlessinger fibre-product condition specializes along small
extensions. -/
#check (CategoryTheory.Functor.HasRimSchlessinger.exists_pullback_isSmallExtension :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x)
    (hf2 : IsSmallExtension (p.map f2)),
    ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
      IsPullback π1 π2 f1 f2 ∧
        IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))

end CategoryTheory.Functor
