module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Comparison

open CategoryTheory AlgebraicGeometry

universe u

/- The canonical comparison maps arrows into the restriction along the object map. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.restrictionArrow :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H),
    G.R ⟶ (H.pullback f.obj).R)

/- Restriction means invertibility of the canonical arrow comparison. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.IsRestriction :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B}, GroupoidAlgebraicSpace.Hom G H → Prop)
