/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentitySections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChangeComparison

/-!
# Geometric-fibre sections and the small étale stalk comparison
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Inverse image of a small étale sheaf of sets along the inclusion of the geometric
fibre `pullback f xbar.hom`. -/
def geometricFiberSheaf (f : Y ⟶ X) (xbar : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    Sheaf (smallEtaleTopology (pullback f xbar.hom)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi (pullback.fst f xbar.hom)).inverseImage.obj F

/-- `geometricFiberSheaf f xbar F` is inverse image along `pullback.fst f xbar.hom`. -/
theorem geometricFiberSheaf_eq (f : Y ⟶ X) (xbar : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    geometricFiberSheaf f xbar F =
      (smallEtaleMorphismOfTopoi (pullback.fst f xbar.hom)).inverseImage.obj F :=
  rfl

variable (f : Y ⟶ X) (xbar : GeometricPoint X)

/-- The morphism from the geometric fibre of `xbar` to the fibre of the composite lift
through an étale neighborhood, induced by the two projections of
`pullback f xbar.hom`. -/
def geometricFiberToNeighborhood (N : SmallEtaleNeighborhood xbar) :
    pullback f xbar.hom ⟶ pullback f (N.lift ≫ N.toSite.hom) :=
  pullback.lift (pullback.fst f xbar.hom) (pullback.snd f xbar.hom) sorry

/-- The first projection of `geometricFiberToNeighborhood` is the geometric-fibre
inclusion. -/
theorem geometricFiberToNeighborhood_fst (N : SmallEtaleNeighborhood xbar) :
    geometricFiberToNeighborhood f xbar N ≫ pullback.fst f (N.lift ≫ N.toSite.hom) =
      pullback.fst f xbar.hom :=
  sorry

variable (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))

/-- Component of the comparison on an étale neighborhood of `xbar`. -/
def smallEtalePushforwardSectionToGeometricFiberSections
    (N : SmallEtaleNeighborhood xbar)
    (t : ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj.obj (op N.toSite)) :
    (geometricFiberSheaf f xbar F).obj.sections :=
  let G := (smallEtaleMorphismOfTopoi f).pushforward.obj F
  let gN := N.lift ≫ N.toSite.hom
  let FN :=
    (smallEtaleMorphismOfTopoi (pullback.fst f gN)).inverseImage.obj F
  let φ := geometricFiberToNeighborhood f xbar N
  (Functor.sectionsFunctor _).map
      (eqToHom
          (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj F)
            (geometricFiberToNeighborhood_fst f xbar N))).hom
    ((Functor.sectionsFunctor _).map
        ((smallEtaleMorphismOfTopoiComp φ (pullback.fst f gN)).app F).inv.hom
      (smallEtaleGlobalSectionsPullback φ FN
        ((smallEtaleMorphismOfTopoi (pullback.snd f gN)).pushforwardSectionsEquiv FN
          (evalIdentityToSections _
            ((smallEtaleBaseChangeHom f (N.lift ≫ N.toSite.hom)
                (pullback.snd f (N.lift ≫ N.toSite.hom))
                (pullback.fst f (N.lift ≫ N.toSite.hom))
                (IsPullback.of_hasPullback f (N.lift ≫ N.toSite.hom)) F).hom.app
              (op (smallEtaleSite.id xbar.overObj))
              (etaleInverseImageSections.restrict N.overHom G
                (pushforwardSectionToInverseImageEval G t)))))))

/-- Canonical comparison `(f_* F)_xbar ⟶ Γ(Y_xbar, F_xbar)` on sheaves of sets, where
`Y_xbar` is the geometric fibre `pullback f xbar.hom` and `F_xbar` is
`geometricFiberSheaf f xbar F`. -/
def smallEtalePushforwardStalkToGeometricFiberSections :
    stalk xbar ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj →
      (geometricFiberSheaf f xbar F).obj.sections :=
  (sectionsDiagram xbar ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj).descColimitType
    { pt := (geometricFiberSheaf f xbar F).obj.sections
      ι := fun j t ↦
        smallEtalePushforwardSectionToGeometricFiberSections f xbar F j.unop t
      ι_naturality := sorry }

/-- The comparison sends the germ of a neighborhood section to the corresponding
neighborhood component. -/
theorem smallEtalePushforwardStalkToGeometricFiberSections_apply
    (N : SmallEtaleNeighborhood xbar)
    (t : ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj.obj (op N.toSite)) :
    smallEtalePushforwardStalkToGeometricFiberSections f xbar F (toStalk N t) =
      smallEtalePushforwardSectionToGeometricFiberSections f xbar F N t :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
