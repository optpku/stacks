/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.NeighborhoodComparison

/-!
# Spaces-étale stalks and comparison with small-étale stalks

A presheaf on `smallEtaleSite X` has a right Kan extension to `spacesEtaleSite X` along
`smallEtaleToSpaces.op`. Its colimit over all étale neighborhoods is canonically isomorphic to
the small-étale stalk. For a sheaf, `correspondingSpacesSheaf` identifies this extension with
the underlying presheaf of the corresponding spaces-étale sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u


namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The right Kan extension of a small-étale presheaf to the spaces-étale site along
`smallEtaleToSpaces.op`. -/
def correspondingSpacesPresheaf (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleToSpaces X).op.ran.obj F

/-- Restriction of the corresponding spaces-étale presheaf along `smallEtaleToSpaces` is the
right Kan extension counit. -/
def correspondingSpacesPresheaf_restrict (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleToSpaces X).op ⋙ correspondingSpacesPresheaf F ⟶ F :=
  (smallEtaleToSpaces X).op.ranCounit.app F

/-- The Kan extension counit is an isomorphism because `smallEtaleToSpaces` is fully faithful. -/
instance isIso_correspondingSpacesPresheaf_restrict (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    IsIso (correspondingSpacesPresheaf_restrict F) :=
  inferInstanceAs (IsIso ((smallEtaleToSpaces X).op.ranCounit.app F))

/-- Restriction along the actual Yoneda preimages of arrows into a scheme chart is natural. -/
theorem correspondingSpacesPresheafSectionCone_naturality
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : smallEtaleSite X)
    {a b : StructuredArrow (op ((smallEtaleToSpaces X).obj U)) (smallEtaleToSpaces X).op}
    (f : a ⟶ b) :
    F.map (smallEtaleToSpacesPreimage X a.hom.unop).op ≫ F.map f.right =
      𝟙 (F.obj (op U)) ≫ F.map (smallEtaleToSpacesPreimage X b.hom.unop).op := by
  simp only [Category.id_comp, ← F.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply (smallEtaleToSpaces X).map_injective
  simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op, Functor.map_comp,
    smallEtaleToSpaces_map_preimage] using! congrArg Quiver.Hom.unop f.w

/-- A section on a scheme chart gives the compatible family of all its restrictions.
The arrows are actual Yoneda preimages, rather than choices from fullness. -/
def correspondingSpacesPresheafSectionCone
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : smallEtaleSite X) :
    Limits.Cone (StructuredArrow.proj (op ((smallEtaleToSpaces X).obj U))
      (smallEtaleToSpaces X).op ⋙ F) where
  pt := F.obj (op U)
  π :=
    { app := fun a ↦ F.map (smallEtaleToSpacesPreimage X a.hom.unop).op
      naturality := by
        intro a b f
        exact (correspondingSpacesPresheafSectionCone_naturality F U f).symm }

/-- Extend a section on a scheme chart by its explicit compatible family in the
pointwise right Kan limit. This construction does not invert the restriction counit. -/
def correspondingSpacesPresheafSection
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : smallEtaleSite X) :
    F.obj (op U) ⟶ (correspondingSpacesPresheaf F).obj (op ((smallEtaleToSpaces X).obj U)) :=
  Limits.limit.lift _ (correspondingSpacesPresheafSectionCone F U) ≫
    ((smallEtaleToSpaces X).op.ranObjObjIsoLimit F
      (op ((smallEtaleToSpaces X).obj U))).inv

/-- The compatible-family extension is the inverse of restriction to the scheme chart. -/
theorem correspondingSpacesPresheafSection_eq_inv
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (U : smallEtaleSite X) :
    correspondingSpacesPresheafSection F U =
      (inv (correspondingSpacesPresheaf_restrict F)).app (op U) := by
  rw [NatIso.isIso_inv_app]
  apply IsIso.eq_inv_of_inv_hom_id
  have hpre : smallEtaleToSpacesPreimage X (𝟙 ((smallEtaleToSpaces X).obj U)) = 𝟙 U := by
    apply (smallEtaleToSpaces X).map_injective
    simp
  have h := (smallEtaleToSpaces X).op.ranObjObjIsoLimit_inv_π F
    (op ((smallEtaleToSpaces X).obj U))
    (StructuredArrow.mk (Y := op U) (𝟙 (op ((smallEtaleToSpaces X).obj U))))
  simp only [StructuredArrow.mk_hom_eq_self, StructuredArrow.mk_right] at h
  erw [((smallEtaleToSpaces X).op.ran.obj F).map_id, Category.id_comp] at h
  change (Limits.limit.lift _ (correspondingSpacesPresheafSectionCone F U) ≫
    ((smallEtaleToSpaces X).op.ranObjObjIsoLimit F
      (op ((smallEtaleToSpaces X).obj U))).inv) ≫
    ((smallEtaleToSpaces X).op.ranCounit.app F).app (op U) = 𝟙 _
  erw [Category.assoc, h, Limits.limit.lift_π]
  change F.map (smallEtaleToSpacesPreimage X (𝟙 ((smallEtaleToSpaces X).obj U))).op = 𝟙 _
  rw [hpre]
  simp

/-- On sheaves, the corresponding spaces-étale presheaf is the underlying presheaf of the
cocontinuous pushforward along `smallEtaleToSpaces`. -/
theorem correspondingSpacesSheaf (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    correspondingSpacesPresheaf F.obj =
      (((smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
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
  rfl

/-- The colimit of a spaces-étale presheaf over all étale neighborhoods of a geometric point. -/
def spacesEtaleStalk (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) : Type (u + 1) :=
  (spacesSectionsDiagram xbar F').ColimitType

/-- The spaces-étale stalk is the colimit type of the sections diagram over all étale
neighborhoods. -/
theorem spacesEtaleStalk_def (xbar : GeometricPoint X)
    (F' : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    spacesEtaleStalk xbar F' = (spacesSectionsDiagram xbar F').ColimitType :=
  rfl

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
  rfl

/-- The component of the stalk comparison at a small étale neighborhood. -/
def stalkToSpacesColimitι (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (j : (SmallEtaleNeighborhood xbar)ᵒᵖ)
    (σ : F.obj ((CategoryOfElements.π (smallLiftFunctor xbar)).op.obj j)) :
    spacesEtaleStalk xbar (correspondingSpacesPresheaf F) :=
  toSpacesEtaleStalk ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj j.unop)
    (correspondingSpacesPresheafSection F
      ((CategoryOfElements.π (smallLiftFunctor xbar)).obj j.unop) σ)

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

/-- The canonical comparison from the small-étale stalk of a presheaf to the colimit of its
right Kan extension over all algebraic-space étale neighborhoods is an isomorphism. -/
instance isIso_stalkToSpacesColimit (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    IsIso (stalkToSpacesColimit xbar F) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
