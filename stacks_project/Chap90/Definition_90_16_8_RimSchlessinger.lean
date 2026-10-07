module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Rim-Schlessinger condition (RS)

A category cofibered in groupoids over `C_Λ` satisfies (RS) when every cospan in the
total category lying over a cospan `A₁ → A ← A₂` in `C_Λ` with `A₂ → A` surjective
admits a fibre product whose image is a fibre product in `C_Λ`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies the Rim-Schlessinger condition
(RS) if it is cofibered in groupoids and every cospan in `F` lying over a cospan in
`ArtinianLocalAlgCat Λ k` with surjective `A₂ → A` admits a fibre product in `F` whose
image square is a pullback in `ArtinianLocalAlgCat Λ k`. -/
class HasRimSchlessinger (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  [isCofiberedInGroupoids : IsFibered.InGroupoids p.op]
  exists_pullback : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
    Function.Surjective (p.map f2).hom →
      ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
        IsPullback π1 π2 f1 f2 ∧
          IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (RS). -/
instance instHasRimSchlessingerId :
    HasRimSchlessinger (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- The Rim-Schlessinger condition is cofiberedness in groupoids together with existence of
fibre products lying over ring-level fibre products along a surjection. -/
theorem hasRimSchlessinger_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasRimSchlessinger p ↔
      IsFibered.InGroupoids p.op ∧
        ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
          Function.Surjective (p.map f2).hom →
            ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
              IsPullback π1 π2 f1 f2 ∧
                IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

end CategoryTheory.Functor
