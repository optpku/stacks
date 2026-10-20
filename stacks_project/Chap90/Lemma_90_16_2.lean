module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Pullback

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

/- Lemma 90.16.2: If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and
satisfies (RS), then any commutative square in `F` lying over a fibre-product square
`A₁ ×_A A₂` in `ArtinianLocalAlgCat Λ k` with `A₂ ⟶ A` surjective is itself a fibre
square in `F`. -/
@[stacks 06J3] #check (CategoryTheory.Functor.HasRimSchlessinger.isPullback :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.HasRimSchlessinger p]
    {x x1 x2 y : F} {f1 : x1 ⟶ x} {f2 : x2 ⟶ x} {π1 : y ⟶ x1} {π2 : y ⟶ x2},
    Function.Surjective (p.map f2).hom → CommSq π1 π2 f1 f2 →
      IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) →
        IsPullback π1 π2 f1 f2)
