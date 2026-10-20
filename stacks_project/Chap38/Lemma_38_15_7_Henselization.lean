module

public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Over

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Henselization.map :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S) (Rh : Type u) [CommRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh],
    AlgebraicGeometry.Spec (CommRingCat.of Rh) ⟶ S)

#check (AlgebraicGeometry.Scheme.Modules.Impurity.Over :
  ∀ {X S T : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    (s : S) (g : T ⟶ S) (t : T), Type u)
