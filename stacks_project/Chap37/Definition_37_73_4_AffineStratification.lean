module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.number :
  (X : AlgebraicGeometry.Scheme.{u}) → [Nonempty X] → [CompactSpace X] →
    [QuasiSeparatedSpace X] → ℕ)
