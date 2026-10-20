module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.NatIso
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AtlasNeighborhoods
public import ReasLib.CategoryTheory.Sites.Point.Construction

/-!
# Small étale site points of algebraic spaces

A geometric point determines a site point whose fibers are its lifts through étale schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A geometric point of an algebraic space determines a point of the small étale site,
whose fiber consists of scheme-over-`S` lifts of the geometric point. -/
noncomputable def toSmallEtalePoint (xbar : GeometricPoint X) :
    (smallEtaleTopology X).Point.{u} where
  fiber := toSmallEtalePoint_fiber xbar
  isCofiltered := sorry
  initiallySmall := smallEtaleFiber_initiallySmall xbar
  jointly_surjective := sorry

/-- The lift-valued fiber of the site point is naturally isomorphic to the functor of
costructured-arrow lifts through small étale neighborhoods. -/
noncomputable def toSmallEtalePoint_fiberIso_smallLiftFunctor (xbar : GeometricPoint X) :
    (toSmallEtalePoint xbar).fiber ≅ smallLiftFunctor xbar :=
  NatIso.ofComponents (fun U ↦
    { hom := TypeCat.ofHom fun l ↦ CategoryTheory.CostructuredArrow.homMk l.hom l.fac
      inv := TypeCat.ofHom fun l ↦ OverLift.of l.left l.w
      hom_inv_id := by rfl
      inv_hom_id := by rfl }) sorry

/-- The presheaf fiber of the site point of a geometric point is equivalent to the colimit
of sections over its small étale neighborhoods, by transporting the chosen lifts. -/
noncomputable def toSmallEtalePoint_stalkEquiv (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    ((toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)).obj F ≃
      stalk xbar F := by
  refine
    { toFun := (toSmallEtalePoint xbar).presheafFiberDesc
        (fun U l ↦ TypeCat.ofHom fun σ ↦
          toStalk (Functor.elementsMk (smallLiftFunctor xbar) U
            ((toSmallEtalePoint_fiberIso_smallLiftFunctor xbar).hom.app U l)) σ) ?_
      invFun := (sectionsDiagram xbar F).descColimitType
        { pt := (toSmallEtalePoint xbar).presheafFiber.obj F
          ι := fun N σ ↦ (toSmallEtalePoint xbar).toPresheafFiber N.unop.1
            ((toSmallEtalePoint_fiberIso_smallLiftFunctor xbar).inv.app N.unop.1
              N.unop.2) F σ
          ι_naturality := ?_ }
      left_inv := ?_
      right_inv := ?_ }
  all_goals sorry

/-- The stalk equivalence sends a section with a chosen lift to its germ in the
corresponding small étale neighborhood. -/
theorem toSmallEtalePoint_stalkEquiv_eq (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : smallEtaleSite X)
    (l : (toSmallEtalePoint xbar).fiber.obj U) (σ : F.obj (op U)) :
    toSmallEtalePoint_stalkEquiv xbar F
        ((toSmallEtalePoint xbar).toPresheafFiber U l F σ) =
      toStalk (Functor.elementsMk (smallLiftFunctor xbar) U
        ((toSmallEtalePoint_fiberIso_smallLiftFunctor xbar).hom.app U l)) σ := sorry

/-- The presheaf fiber functor of the site point of a geometric point is naturally
isomorphic to its geometric stalk functor. -/
noncomputable def toSmallEtalePoint_stalkIso (xbar : GeometricPoint X) :
    ((toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)) ≅
      stalkFunctor xbar :=
  NatIso.ofComponents (fun F ↦ (toSmallEtalePoint_stalkEquiv xbar F).toIso) sorry

/-- The components of the stalk natural isomorphism are the equivalences induced by
transporting lifts in the neighborhood colimits. -/
theorem toSmallEtalePoint_stalkIso_app (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (toSmallEtalePoint_stalkIso xbar).app F =
      (toSmallEtalePoint_stalkEquiv xbar F).toIso := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
