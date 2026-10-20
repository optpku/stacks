module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger

/-!
# Pullback squares under the Rim-Schlessinger condition

Commutative squares over pullbacks along surjective algebra maps are pullbacks
in the total category of a functor satisfying the Rim-Schlessinger condition.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor.HasRimSchlessinger

/-- For a functor satisfying the Rim-Schlessinger condition, a commutative square
whose image is a pullback and whose right cospan leg maps to a surjective algebra
map is itself a pullback in the total category. -/
theorem isPullback (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    {x x1 x2 y : F} {f1 : x1 ⟶ x} {f2 : x2 ⟶ x} {π1 : y ⟶ x1} {π2 : y ⟶ x2}
    (hf2 : Function.Surjective (p.map f2).hom) (h_sq : CommSq π1 π2 f1 f2)
    (h_base : IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)) :
    IsPullback π1 π2 f1 f2 := sorry

end CategoryTheory.Functor.HasRimSchlessinger
