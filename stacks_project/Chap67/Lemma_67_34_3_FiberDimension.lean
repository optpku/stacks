module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension

/-! Numeric fibre invariants and their étale scheme-square specifications. -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X), WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.fiberStalkDimAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X), WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionAt_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x),
    fiberDimensionAt f x = Scheme.Hom.fiberDimensionAt h.left u)

#check (AlgebraicGeometry.AlgebraicSpace.fiberStalkDimAt_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x),
    fiberStalkDimAt f x = ringKrullDim (Scheme.Hom.fiberStalkAt h.left u))

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionAt_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left),
    fiberDimensionAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      Scheme.Hom.fiberDimensionAt h.left u)

#check (AlgebraicGeometry.AlgebraicSpace.fiberStalkDimAt_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left),
    fiberStalkDimAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      ringKrullDim (Scheme.Hom.fiberStalkAt h.left u))

#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_iff_fiberDimensionAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ) (x : Points X),
    RelativeDimensionAt f d x ↔ fiberDimensionAt f x = (d : WithBot ℕ∞))

#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionLEAt_iff_fiberDimensionAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ) (x : Points X),
    RelativeDimensionLEAt f d x ↔ fiberDimensionAt f x ≤ (d : WithBot ℕ∞))
