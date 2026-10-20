module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Zariski-local factorization of algebraic-space morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : Y ⟶ X` Zariski-locally factors through `u : U ⟶ X` if every
point of `Y` has an open neighbourhood on which `f` factors through `u`. -/
def zariskiLocallyFactorsThrough {S : Scheme.{u}} {Y X U : AlgebraicSpace S}
    (f : Y ⟶ X) (u : U ⟶ X) : Prop :=
  ∀ y : Points Y, ∃ V : OpenSubspace Y,
    y ∈ V.pointsSet ∧ ∃ g : V.X ⟶ U, V.ι ≫ f = g ≫ u

/-- The predicate `zariskiLocallyFactorsThrough f u` unfolds to local open
neighbourhoods carrying a factorization of `f` through `u`. -/
theorem zariskiLocallyFactorsThrough_iff {S : Scheme.{u}}
    {Y X U : AlgebraicSpace S} (f : Y ⟶ X) (u : U ⟶ X) :
    zariskiLocallyFactorsThrough f u ↔
      ∀ y : Points Y, ∃ V : OpenSubspace Y,
        y ∈ V.pointsSet ∧ ∃ g : V.X ⟶ U, V.ι ≫ f = g ≫ u :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
