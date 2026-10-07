module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger

/-!
# Fibre squares under (RS)

Under the Rim-Schlessinger condition, a commutative square in the total category
that lies over a ring-level fibre product along a surjection is itself a fibre square.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor.HasRimSchlessinger

/-- Lemma 90.16.2: If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and
satisfies (RS), then any commutative square in `F` lying over a fibre-product square
`A₁ ×_A A₂` in `ArtinianLocalAlgCat Λ k` with `A₂ ⟶ A` surjective is itself a fibre
square in `F`.

The Stacks xymatrix draws `y` over `A₁ ×_A A₂` with a surjection `A₂ ⟶ A`. The binders
follow `exists_pullback`: `π1 : y ⟶ x1`, `π2 : y ⟶ x2`, and surjectivity on `p.map f2`. -/
@[stacks 06J3]
theorem isPullback (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    {x x1 x2 y : F} {f1 : x1 ⟶ x} {f2 : x2 ⟶ x} {π1 : y ⟶ x1} {π2 : y ⟶ x2}
    (hf2 : Function.Surjective (p.map f2).hom) (h_sq : CommSq π1 π2 f1 f2)
    (h_base : IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)) :
    IsPullback π1 π2 f1 f2 := sorry

end CategoryTheory.Functor.HasRimSchlessinger
