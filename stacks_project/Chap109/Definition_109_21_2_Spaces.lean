module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Semistability of algebraic-space morphisms and families of curves. -/
#check (AlgebraicGeometry.AlgebraicSpace.Semistable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.instSemistable_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Semistable h.left] [IsProper h.left],
    AlgebraicGeometry.AlgebraicSpace.Semistable (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistable :
  ∀ S : Scheme.{u}, ObjectProperty (Spaces.Curves.Obj S))
