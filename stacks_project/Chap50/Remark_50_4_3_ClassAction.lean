module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.DeRham
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme.DeRham.ClassAction

/-- The constant-one class is independent of the supplied derived tensor presentation. -/
noncomputable def cohomologyOne {X S : Scheme.{u}} (p : X ⟶ S)
    [MonoidalCategory (RingedSite.Hom.ModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
    [(RingedSite.Hom.moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).LaxMonoidal] :
    cohomology p 0 := cohomologyOneCanonical p

end AlgebraicGeometry.Scheme.DeRham.ClassAction

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.map :
  {X S : Scheme.{u}} → (p : X ⟶ S) → (n : ℤ) →
    cohomology p n → ShiftedHom (derivedComplex p) (derivedComplex p) n)
