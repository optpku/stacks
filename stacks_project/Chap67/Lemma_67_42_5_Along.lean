module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Factorization

/-!
# Valuative squares of algebraic spaces with factored generic arrows

The shared mathematical owner supplies factored valuative squares and the
restricted uniqueness and existence predicates. These typed checks preserve
the chapter import surface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Along.Uniqueness :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}, (U ⟶ X) → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Along.Existence :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}, (U ⟶ X) → (X ⟶ Y) → Prop)
