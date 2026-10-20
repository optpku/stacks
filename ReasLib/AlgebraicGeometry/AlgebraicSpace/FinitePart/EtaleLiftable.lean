module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-! # Étale liftability of finite-part points -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- A finite-part pair over `T` is étale-liftable if it is the restriction of a pair
`(a, Z)` along some morphism `T ⟶ U` with `a : U ⟶ Y` étale. -/
def IsEtaleLiftable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {T : Over S} (p : Point f T) : Prop :=
  ∃ (U : Over S) (h : T ⟶ U) (q : Point f U),
    Etale q.a ∧ q.restrict h = p

end AlgebraicGeometry.AlgebraicSpace.FinitePart
