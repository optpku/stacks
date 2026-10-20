module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The object property of abelian sheaves on the small étale site whose support is contained
in the closed points of the scheme. -/
abbrev supportSubsetClosedPoints (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  fun F ↦ abelianSheafSupport F ⊆ closedPoints X

/-- An abelian étale sheaf has support contained in the closed points if and only if every
geometric point with nonzero geometric stalk has closed image. -/
theorem supportSubsetClosedPoints_iff_geometricStalk {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    supportSubsetClosedPoints X F ↔
      ∀ xbar : Scheme.GeometricPoint X,
        ¬ IsZero (geometricStalk F xbar) → xbar.image ∈ closedPoints X := sorry

/-- A derived object of abelian étale sheaves has cohomology supported in closed points if and
only if a geometric stalk of some cohomology sheaf can be nonzero only at a closed point. -/
theorem cohomologyIn_supportSubsetClosedPoints_iff_geometricStalk {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.cohomologyIn (supportSubsetClosedPoints X) Q ↔
      ∀ xbar : Scheme.GeometricPoint X,
        (∃ n : ℤ, ¬ IsZero (geometricStalk
            ((DerivedCategory.homologyFunctor
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) n).obj Q) xbar)) →
          xbar.image ∈ closedPoints X := sorry

end AlgebraicGeometry.Scheme.Etale

end
