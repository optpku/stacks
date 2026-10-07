module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Comparison

@[expose] public section

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.FormallyEtale.toFormallySmooth :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.FormallyEtale f], AlgebraicGeometry.FormallySmooth f)

#check
  (AlgebraicGeometry.FormallyEtale.iff_formallySmooth_and_formallyUnramified :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.FormallyEtale f ↔
        AlgebraicGeometry.FormallySmooth f ∧ AlgebraicGeometry.FormallyUnramified f)
