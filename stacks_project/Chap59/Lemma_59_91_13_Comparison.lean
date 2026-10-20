module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

universe u

#check (AlgebraicGeometry.Scheme.Hom.geometricFiber :
  {X Y : Scheme.{u}} → (X ⟶ Y) → GeometricPoint Y → Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.geometricFiber_def :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    geometricFiber f ybar = pullback ybar.hom f)

#check (AlgebraicGeometry.Scheme.Hom.geometricFiberToPoint :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    geometricFiber f ybar ⟶ Spec (.of ybar.K))

#check (AlgebraicGeometry.Scheme.Hom.geometricFiberToPoint_def :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    geometricFiberToPoint f ybar = pullback.fst ybar.hom f)

#check (AlgebraicGeometry.Scheme.Hom.geometricFiberToX :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    geometricFiber f ybar ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.geometricFiberToX_def :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    geometricFiberToX f ybar = pullback.snd ybar.hom f)

#check (AlgebraicGeometry.Scheme.Hom.geometricFiber_isPullback :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    IsPullback (geometricFiberToX f ybar) (geometricFiberToPoint f ybar) f ybar.hom)
