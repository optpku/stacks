module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Locus

@[expose] public section

open AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.Scheme.cohenMacaulayLocus :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      Set X)

#check
  (AlgebraicGeometry.Scheme.mem_cohenMacaulayLocus :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
      (x : X),
      x ∈ X.cohenMacaulayLocus ↔
        Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x))
