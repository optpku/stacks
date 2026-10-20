module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber

/-!
# Set-theoretic fibres of morphisms of algebraic spaces

The set-theoretic fibre and its membership, computation, representative-transport,
and canonical field-fibre map laws are provided by the mathematical owner.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → Points Y → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_fiberOver_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {y : Points Y} {x : Points X},
    x ∈ fiberOver f y ↔ Points.map f x = y)

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_eq :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    fiberOver f y = Points.map f ⁻¹' {y})

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_eq_of_mk :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y) {y : Points Y}
    (hy : Points.mk p = y),
    fiberOver f y = fiberOver f (Points.mk p))

#check (AlgebraicGeometry.AlgebraicSpace.mapsTo_fieldFiberι_fiberOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    Set.MapsTo (Points.map (fieldFiberι f p)) Set.univ
      (fiberOver f (Points.mk p)))

#check (AlgebraicGeometry.AlgebraicSpace.surjOn_pointsMap_fieldFiberι :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    Set.SurjOn (Points.map (fieldFiberι f p)) Set.univ
      (fiberOver f (Points.mk p)))
