module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Definition_66_19_6_Stalk
public import stacks_project.Chap66.«66_19_6_1_Neighborhood»

/-!
# Spaces-étale colimit of the corresponding sheaf

The sheaf on `spacesEtaleSite X` corresponding to a presheaf `F` on `smallEtaleSite X` is the
right Kan extension along `smallEtaleInclusion.op`. Its colimit over all étale neighborhoods is
the comparison target for the small-étale stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `smallEtaleInclusion` is full, as the comma comparison `CostructuredArrow.toOver` along the
fully faithful functor `ofOverFunctor`. -/
instance smallEtaleInclusion_full {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).Full :=
  inferInstanceAs
    ((MorphismProperty.CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) X).Full)

/-- `smallEtaleInclusion` is faithful, as the comma comparison `CostructuredArrow.toOver` along
the faithful functor `ofOverFunctor`. -/
instance smallEtaleInclusion_faithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).Faithful :=
  inferInstanceAs
    ((MorphismProperty.CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) X).Faithful)

/-- The opposite of `smallEtaleInclusion` is full. -/
instance smallEtaleInclusion_op_full {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).op).Full :=
  inferInstance

/-- The opposite of `smallEtaleInclusion` is faithful. -/
instance smallEtaleInclusion_op_faithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).op).Faithful :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The presheaf on `spacesEtaleSite X` corresponding to a presheaf on `smallEtaleSite X`, as the
right Kan extension along `smallEtaleInclusion.op`. -/
def correspondingSpacesPresheaf (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleInclusion X).op.ran.obj F

/-- Restriction of the corresponding spaces-étale presheaf along `smallEtaleInclusion` is the
right Kan extension counit. -/
def correspondingSpacesPresheaf_restrict (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleInclusion X).op ⋙ correspondingSpacesPresheaf F ⟶ F :=
  (smallEtaleInclusion X).op.ranCounit.app F

/-- The Kan extension counit is an isomorphism because `smallEtaleInclusion` is fully faithful. -/
instance isIso_correspondingSpacesPresheaf_restrict (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    IsIso (correspondingSpacesPresheaf_restrict F) :=
  inferInstanceAs (IsIso ((smallEtaleInclusion X).op.ranCounit.app F))

/-- On sheaves, the corresponding spaces-étale presheaf is the underlying presheaf of the
cocontinuous pushforward along `smallEtaleInclusion`. -/
theorem correspondingSpacesSheaf (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    correspondingSpacesPresheaf F.obj =
      (((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)).obj F).obj :=
  sorry

/-- The diagram of sections of a spaces-étale presheaf over all étale neighborhoods of a
geometric point. -/
def spacesSectionsDiagram (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (EtaleNeighborhood xbar)ᵒᵖ ⥤ Type (u + 1) :=
  (CategoryOfElements.π (etaleLiftFunctor xbar)).op ⋙ F'

/-- The value of `spacesSectionsDiagram` at a neighborhood is the value of the presheaf on the
underlying spaces-étale object. -/
theorem spacesSectionsDiagram_obj (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : EtaleNeighborhood xbar) :
    (spacesSectionsDiagram xbar F').obj (op U) = F'.obj (op U.toSpacesEtale) :=
  sorry

/-- The colimit of a spaces-étale presheaf over all étale neighborhoods of a geometric point. -/
def spacesEtaleStalk (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) : Type (u + 1) :=
  (spacesSectionsDiagram xbar F').ColimitType

/-- The spaces-étale stalk is the colimit type of the sections diagram over all étale
neighborhoods. -/
theorem spacesEtaleStalk_def (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    spacesEtaleStalk xbar F' = (spacesSectionsDiagram xbar F').ColimitType :=
  sorry

/-- The germ map from sections over an étale neighborhood to the spaces-étale stalk. -/
def toSpacesEtaleStalk {xbar : GeometricPoint X} {F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)}
    (U : EtaleNeighborhood xbar) (σ : F'.obj (op U.toSpacesEtale)) :
    spacesEtaleStalk xbar F' :=
  (spacesSectionsDiagram xbar F').ιColimitType (op U) σ

/-- The germ of a spaces-étale section is the canonical colimit inclusion of that section. -/
theorem toSpacesEtaleStalk_apply {xbar : GeometricPoint X}
    {F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)} (U : EtaleNeighborhood xbar)
    (σ : F'.obj (op U.toSpacesEtale)) :
    toSpacesEtaleStalk U σ = (spacesSectionsDiagram xbar F').ιColimitType (op U) σ :=
  sorry

/-- The component of the stalk comparison at a small étale neighborhood. -/
def stalkToSpacesColimitι (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (j : (SmallEtaleNeighborhood xbar)ᵒᵖ)
    (σ : F.obj ((CategoryOfElements.π (smallLiftFunctor xbar)).op.obj j)) :
    spacesEtaleStalk xbar (correspondingSpacesPresheaf F) :=
  toSpacesEtaleStalk ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj j.unop)
    ((inv (correspondingSpacesPresheaf_restrict F)).app
      ((CategoryOfElements.π (smallLiftFunctor xbar)).op.obj j) σ)

/-- The comparison components are compatible with restriction along morphisms of small étale
neighborhoods. -/
theorem stalkToSpacesColimitι_naturality (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) {j j' : (SmallEtaleNeighborhood xbar)ᵒᵖ}
    (f : j ⟶ j') :
    (stalkToSpacesColimitι xbar F j').comp ((sectionsDiagram xbar F).map f) =
      stalkToSpacesColimitι xbar F j :=
  sorry

/-- The cocone of small-étale sections with vertex the spaces-étale stalk of the corresponding
presheaf. -/
def stalkToSpacesCocone (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (sectionsDiagram xbar F).CoconeTypes where
  pt := spacesEtaleStalk xbar (correspondingSpacesPresheaf F)
  ι := stalkToSpacesColimitι xbar F
  ι_naturality := stalkToSpacesColimitι_naturality xbar F

/-- The canonical comparison from the small-étale stalk of `F` to the colimit of the corresponding
spaces-étale presheaf over all étale neighborhoods. -/
def stalkToSpacesColimit (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    stalk xbar F ⟶ spacesEtaleStalk xbar (correspondingSpacesPresheaf F) :=
  ↾((sectionsDiagram xbar F).descColimitType (stalkToSpacesCocone xbar F))

/-- On germs, the comparison is the spaces-étale germ of the Kan-extended section. -/
theorem stalkToSpacesColimit_toStalk {xbar : GeometricPoint X}
    {F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)} (N : SmallEtaleNeighborhood xbar)
    (σ : F.obj (op N.toSite)) :
    stalkToSpacesColimit xbar F (toStalk N σ) =
      toSpacesEtaleStalk ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N)
        ((inv (correspondingSpacesPresheaf_restrict F)).app (op N.toSite) σ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
