module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ResidueFiber

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions

universe u

/- Infinitesimal neighbourhoods: the canonical map from the strict-local spectrum. -/
#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.fromSpecEtaleLocalRing :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} (ybar : GeometricPoint Y),
    specSpace ybar ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.space :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    {X : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) (n : ℕ),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.toX :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    {X : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) (n : ℕ),
    space f ybar n ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.toSpec :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    {X : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) (n : ℕ),
    space f ybar n ⟶ thickening ybar n)

#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.sheaf :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    {X : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (ybar : GeometricPoint Y) (n : ℕ), (space f ybar n).Modules)

#check (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.fiber :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    {X : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y), AlgebraicSpace S)
