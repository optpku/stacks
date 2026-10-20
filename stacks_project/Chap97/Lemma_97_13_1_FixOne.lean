module

public import ReasLib.RingTheory.Algebra.FreeDimensional.UnitFixing

import StacksCheckRecall
open AlgebraicGeometry

/-! Compatibility checks for the unit-fixing subgroup API. -/
#check (AlgebraicGeometry.glFixOne :
  ∀ (R : Type) [CommRing R] (d : ℕ) [NeZero d],
    Subgroup (LinearMap.GeneralLinearGroup R (Fin d → R)))
#check (AlgebraicGeometry.GLFixOne.mem_iff :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d]
    (g : LinearMap.GeneralLinearGroup R (Fin d → R)),
    g ∈ AlgebraicGeometry.glFixOne R d ↔
      g • AlgebraicGeometry.FreeDimAlgebra.one R d =
        AlgebraicGeometry.FreeDimAlgebra.one R d)
#check (AlgebraicGeometry.GLFixOne.map_apply :
  ∀ {R S : Type} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (g : AlgebraicGeometry.glFixOne R d),
    (AlgebraicGeometry.GLFixOne.map f g).val =
      Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map f
          (Matrix.GeneralLinearGroup.toLin.symm g.val)))
