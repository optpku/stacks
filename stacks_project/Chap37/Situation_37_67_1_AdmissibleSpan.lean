module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan

open CategoryTheory

universe u

#check (@AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {Z X Y : CategoryTheory.Over S} →
      (Z ⟶ X) → (Z ⟶ Y) → Prop)
