module

public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_19_6_Stalk
public import stacks_project.Chap66.Lemma_66_18_11
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap84.Lemma_84_4_2_Sections
public import stacks_project.Chap84.Lemma_84_4_4_Comparison

/-!
# Geometric-fibre comparison of small étale pushforwards

The inverse image `F_xbar` of a small étale sheaf of sets along the geometric-fibre
inclusion, and the canonical comparison `(f_* F)_xbar ⟶ Γ(Y_xbar, F_xbar)`.
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

/-- The identity-on-left comparison from the identity object of `U`, postcomposed along
`U.hom`, to `U` itself. -/
def etaleRestriction_idHom (U : smallEtaleSite X) :
    (etaleRestriction U.hom).obj (smallEtaleSite.id U.left) ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk (𝟙 U.left) trivial sorry

/-- `etaleRestriction_idHom U` retains the identity on the underlying scheme over `S`. -/
theorem etaleRestriction_idHom_left (U : smallEtaleSite X) :
    (etaleRestriction_idHom U).left = 𝟙 U.left :=
  rfl

/-- Evaluation of `U.hom⁻¹ G` at the identity object of `U`, obtained from a section of `G`
over `U`. -/
def pushforwardSectionToInverseImageEval {U : smallEtaleSite X}
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1))) (t : G.obj.obj (op U)) :
    etaleInverseImageSections U.hom G :=
  (smallEtaleMorphismOfTopoi_inverseImage_obj U.hom G
      (smallEtaleSite.id U.left)).inv
    (G.obj.map (op (etaleRestriction_idHom U)) t)

/-- `pushforwardSectionToInverseImageEval` is `smallEtaleMorphismOfTopoi_inverseImage_obj`
of restriction along `etaleRestriction_idHom`. -/
theorem pushforwardSectionToInverseImageEval_eq {U : smallEtaleSite X}
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1))) (t : G.obj.obj (op U)) :
    pushforwardSectionToInverseImageEval G t =
      (smallEtaleMorphismOfTopoi_inverseImage_obj U.hom G
          (smallEtaleSite.id U.left)).inv
        (G.obj.map (op (etaleRestriction_idHom U)) t) :=
  rfl

/-- Compatible sections of a small étale sheaf on `ofOver T` obtained by restricting an
identity-object value along `smallEtaleSite.homToId`. -/
def evalIdentityToSections {T : Over S}
    (G : Sheaf (smallEtaleTopology (ofOver T)) (Type (u + 1)))
    (s : G.obj.obj (op (smallEtaleSite.id T))) :
    G.obj.sections :=
  ⟨fun U ↦ G.obj.map (smallEtaleSite.homToId T U.unop).op s, sorry⟩

/-- Values of `evalIdentityToSections` at an object `U` are restriction of the
identity-object section along `smallEtaleSite.homToId`. -/
theorem evalIdentityToSections_apply {T : Over S}
    (G : Sheaf (smallEtaleTopology (ofOver T)) (Type (u + 1)))
    (s : G.obj.obj (op (smallEtaleSite.id T))) (U : (smallEtaleSite (ofOver T))ᵒᵖ) :
    (evalIdentityToSections G s).val U =
      G.obj.map (smallEtaleSite.homToId T U.unop).op s :=
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

/-- The adjunction-mate comparison of the cartesian square of `f` against the composite
lift of an étale neighborhood of `xbar`. -/
def smallEtaleBaseChangeHom_neighborhood (N : SmallEtaleNeighborhood xbar) :
    (smallEtaleMorphismOfTopoi (N.lift ≫ N.toSite.hom)).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
      (smallEtaleMorphismOfTopoi
          (pullback.snd f (N.lift ≫ N.toSite.hom))).pushforward.obj
        ((smallEtaleMorphismOfTopoi
            (pullback.fst f (N.lift ≫ N.toSite.hom))).inverseImage.obj F) :=
  smallEtaleBaseChangeHom f (N.lift ≫ N.toSite.hom)
    (pullback.snd f (N.lift ≫ N.toSite.hom))
    (pullback.fst f (N.lift ≫ N.toSite.hom))
    (IsPullback.of_hasPullback f (N.lift ≫ N.toSite.hom)) F

/-- `smallEtaleBaseChangeHom_neighborhood` is `smallEtaleBaseChangeHom` at the chosen
pullback square of the neighborhood lift. -/
theorem smallEtaleBaseChangeHom_neighborhood_eq (N : SmallEtaleNeighborhood xbar) :
    smallEtaleBaseChangeHom_neighborhood f xbar F N =
      smallEtaleBaseChangeHom f (N.lift ≫ N.toSite.hom)
        (pullback.snd f (N.lift ≫ N.toSite.hom))
        (pullback.fst f (N.lift ≫ N.toSite.hom))
        (IsPullback.of_hasPullback f (N.lift ≫ N.toSite.hom)) F :=
  rfl

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
            ((smallEtaleBaseChangeHom_neighborhood f xbar F N).hom.app
              (op (smallEtaleSite.id xbar.overObj))
              (etaleInverseImageSections.restrict N.overHom G
                (pushforwardSectionToInverseImageEval G t)))))))

/-- The first projection of the neighborhood fibre comparison is the geometric-fibre
inclusion, so inverse image along the composite recovers `geometricFiberSheaf`. -/
theorem geometricFiberToNeighborhood_comp_inverseImage
    (N : SmallEtaleNeighborhood xbar) :
    (smallEtaleMorphismOfTopoi
        (geometricFiberToNeighborhood f xbar N ≫
          pullback.fst f (N.lift ≫ N.toSite.hom))).inverseImage.obj F =
      geometricFiberSheaf f xbar F :=
  sorry

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

/-- The comparison is the colimit-type descent of the neighborhood components. -/
theorem smallEtalePushforwardStalkToGeometricFiberSections_eq :
    smallEtalePushforwardStalkToGeometricFiberSections f xbar F =
      (sectionsDiagram xbar
          ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj).descColimitType
        { pt := (geometricFiberSheaf f xbar F).obj.sections
          ι := fun j ↦
            smallEtalePushforwardSectionToGeometricFiberSections f xbar F j.unop
          ι_naturality := sorry } :=
  sorry

/-- The comparison sends the germ of a neighborhood section to the corresponding
neighborhood component. -/
theorem smallEtalePushforwardStalkToGeometricFiberSections_apply
    (N : SmallEtaleNeighborhood xbar)
    (t : ((smallEtaleMorphismOfTopoi f).pushforward.obj F).obj.obj (op N.toSite)) :
    smallEtalePushforwardStalkToGeometricFiberSections f xbar F (toStalk N t) =
      smallEtalePushforwardSectionToGeometricFiberSections f xbar F N t :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
