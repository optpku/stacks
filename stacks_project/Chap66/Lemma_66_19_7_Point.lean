module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Sites.Point.Construction
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Definition_66_19_6_Neighborhood
public import stacks_project.Chap66.Definition_66_19_6_Stalk

/-!
# Small étale site points of algebraic spaces

A geometric point of an algebraic space determines a point of the small étale site whose
fiber functor is the coyoneda functor of lifts through étale neighborhoods. The associated
site-point stalk functor is the geometric stalk of Definition 66.19.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace SmallEtaleNeighborhood

/-- The category of small étale neighborhoods of a geometric point is cofiltered. -/
instance instIsCofiltered (xbar : GeometricPoint X) :
    IsCofiltered (SmallEtaleNeighborhood xbar) := sorry

/-- The category of small étale neighborhoods of a geometric point is initially small. -/
instance instInitiallySmall (xbar : GeometricPoint X) :
    InitiallySmall.{u} (SmallEtaleNeighborhood xbar) := sorry

end SmallEtaleNeighborhood

/-- Covering sieves in the small étale topology of `X` lift jointly surjectively through
`smallLiftFunctor xbar`. -/
theorem coversLift_smallLiftFunctor (xbar : GeometricPoint X) :
    GrothendieckTopology.Point.Fiber.coversLift (smallEtaleTopology X)
      (smallLiftFunctor xbar) := sorry

/-- A geometric point of an algebraic space determines a point of the small étale site,
whose fiber functor sends `U` to the type of lifts of the geometric point through `U`. -/
noncomputable def toSmallEtalePoint (xbar : GeometricPoint X) :
    (smallEtaleTopology X).Point.{u} where
  fiber := smallLiftFunctor xbar
  jointly_surjective := sorry

/-- The fiber functor of `toSmallEtalePoint xbar` is `smallLiftFunctor xbar`. -/
theorem toSmallEtalePoint_fiber (xbar : GeometricPoint X) :
    (toSmallEtalePoint xbar).fiber = smallLiftFunctor xbar := sorry

/-- The value of the fiber of `toSmallEtalePoint xbar` at `U` is the type of Hom-lifts of
`xbar` through `U`, which the source identifies with the underlying set of the geometric
fiber `|U_xbar|`. -/
theorem toSmallEtalePoint_fiber_obj (xbar : GeometricPoint X) (U : smallEtaleSite X) :
    (toSmallEtalePoint xbar).fiber.obj U = (smallLiftFunctor xbar).obj U := sorry

/-- Objectwise, the site-point presheaf fiber of `toSmallEtalePoint xbar` is equivalent to
the geometric stalk of Definition 66.19.6, via the comparison of a colimit with its
colimit type. -/
noncomputable def toSmallEtalePoint_stalkEquiv (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    ((toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)).obj F ≃
      stalk xbar F :=
  Types.colimitEquivColimitType (sectionsDiagram xbar F)

/-- `toSmallEtalePoint_stalkEquiv` is the canonical comparison of a colimit with its
colimit type. -/
theorem toSmallEtalePoint_stalkEquiv_eq (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    toSmallEtalePoint_stalkEquiv xbar F =
      Types.colimitEquivColimitType (sectionsDiagram xbar F) := sorry

/-- The site-point stalk functor associated to `toSmallEtalePoint xbar` (Sites, Equation
7.32.1.1) is the geometric stalk functor `stalkFunctor xbar`. -/
noncomputable def toSmallEtalePoint_stalkIso (xbar : GeometricPoint X) :
    ((toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)) ≅
      stalkFunctor xbar :=
  NatIso.ofComponents (fun F ↦ (toSmallEtalePoint_stalkEquiv xbar F).toIso) sorry

/-- Components of `toSmallEtalePoint_stalkIso` are the objectwise equivalences
`toSmallEtalePoint_stalkEquiv`. -/
theorem toSmallEtalePoint_stalkIso_app (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (toSmallEtalePoint_stalkIso xbar).app F =
      (toSmallEtalePoint_stalkEquiv xbar F).toIso := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
