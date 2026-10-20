module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.OpenSubschemes
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Over

/-!
# Birationality via Generic-Point Residue Fields

This file characterizes birationality of integral schemes locally of finite type over a base by
isomorphism of the residue-field-valued points at chosen generic points.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- For integral schemes locally of finite type over `S`, birationality over `S`, isomorphism of
nonempty open subschemes over `S`, and isomorphism over `S` of the residue-field-valued points at
chosen generic points are equivalent. -/
theorem birationalOver_tfae_of_isIntegral_of_locallyOfFiniteType
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType (X ↘ S)] [LocallyOfFiniteType (Y ↘ S)]
    (x : X) (y : Y)
    (hx : IsGenericPoint x (Set.univ : Set X))
    (hy : IsGenericPoint y (Set.univ : Set Y)) :
    List.TFAE
      [ Scheme.BirationalOver (X ↘ S) (Y ↘ S)
      , HasIsomorphicNonemptyOpenSubschemesOver S X Y
      , Scheme.Hom.IsomorphicResidueFieldPointsOver S X Y x y
      ] := sorry

end AlgebraicGeometry.Scheme
