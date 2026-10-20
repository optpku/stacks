module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Canonical base-change maps between scheme-valued fibers. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.fiberMap :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    {σ τ : AlgebraicGeometry.AlgebraicSpace.CohStack.SchemesOver B},
    (σ ⟶ τ) →
      (AlgebraicGeometry.AlgebraicSpace.CohStack.fiber f σ ⟶
        AlgebraicGeometry.AlgebraicSpace.CohStack.fiber f τ))
