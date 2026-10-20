module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteFibers

open CategoryTheory

universe u

/- Finiteness of a scheme chart fibre is finiteness of the point-map preimage. -/
#check (AlgebraicGeometry.AlgebraicSpace.finiteFibreOver_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {U : CategoryTheory.Over S} (φ : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.finiteFibreOver φ x ↔
      (AlgebraicGeometry.AlgebraicSpace.Points.mapOfOver φ ⁻¹' {x}).Finite)
