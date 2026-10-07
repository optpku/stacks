module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      S.Etale ⥤ AlgebraicGeometry.Scheme.DescentData.Etale f)
