module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-! Compatibility facade for the canonical public owner. -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [LocallyOfFiniteType f] → Points X → ℕ)
