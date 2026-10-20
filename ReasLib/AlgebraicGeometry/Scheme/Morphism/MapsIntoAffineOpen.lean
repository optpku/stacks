module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Factorization through an affine open

A scheme morphism maps into an affine open when it factors through an open
immersion from an affine scheme into its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes factors through some affine open immersion into the
target. -/
def MapsIntoAffineOpen {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (U : Scheme.{u}) (_ : IsAffine U) (i : U ⟶ S) (_ : IsOpenImmersion i) (g : X ⟶ U),
    g ≫ i = f

/-- Factoring through an affine open immersion is equivalent to the existence of
an affine scheme, an open immersion into the target, and a factorization. -/
theorem mapsIntoAffineOpen_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    f.MapsIntoAffineOpen ↔
      ∃ (U : Scheme.{u}) (_ : IsAffine U) (i : U ⟶ S) (_ : IsOpenImmersion i) (g : X ⟶ U),
        g ≫ i = f :=
  sorry

/-- An open immersion from an affine scheme maps into an affine open. -/
theorem mapsIntoAffineOpen_of_isOpenImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsOpenImmersion f] : f.MapsIntoAffineOpen :=
  sorry

end AlgebraicGeometry.Scheme.Hom

