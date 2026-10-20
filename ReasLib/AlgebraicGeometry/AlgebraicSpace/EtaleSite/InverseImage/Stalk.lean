module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SpacesEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

/-!
# Stalks of inverse images on étale sites of algebraic spaces

The stalk of inverse image at a geometric point is canonically identified with the
original stalk at the image geometric point, through the comparison of scheme charts
with the spaces étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.Point

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (xbar : GeometricPoint X)
open GeometricPoint

section

-- Local declaration justification (metaprogramming implementation): public fiber maps use
-- private over-category ascriptions and comparisons without exposing implementation API.
set_option backward.privateInPublic true

/-- Underlying Over-morphism of a comap fibre element at `V`. -/
private noncomputable def smallEtaleInverseImage_comapFiberAsOver
    (V : spacesEtaleSite Y)
    (α : (((toSpacesEtalePoint xbar).comapOfMorphismOfSites
          (h_small := initiallySmall_of_essentiallySmall _) (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber.obj V) :
    Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V) :=
  α

/-- Underlying Over-morphism of a fibre element at `ȳ = f ∘ x̄` and `V`. -/
private noncomputable def smallEtaleInverseImage_imageFiberAsOver
    (V : spacesEtaleSite Y)
    (β : (toSpacesEtalePoint (xbar.map f)).fiber.obj V) :
    Over.mk (xbar.hom ≫ f) ⟶ (MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V :=
  β

/-- An over-category lift through a pulled-back étale object determines an element of
the comapped geometric fiber. -/
private noncomputable def smallEtaleInverseImage_comapFiberFromOver
    (V : spacesEtaleSite Y)
    (α : Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V)) :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites
          (h_small := initiallySmall_of_essentiallySmall _) (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber.obj V :=
  α

/-- An over-category lift of the image geometric point determines an element of its
geometric fiber. -/
private noncomputable def smallEtaleInverseImage_imageFiberFromOver
    (V : spacesEtaleSite Y)
    (β : Over.mk (xbar.hom ≫ f) ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V) :
    (toSpacesEtalePoint (xbar.map f)).fiber.obj V :=
  β

/-- `Over.map f` applied to `Over.mk xbar.hom` is the over-object of `ȳ = f ∘ x̄`. -/
private noncomputable def smallEtaleInverseImage_imageOverIso :
    (CategoryTheory.Over.map f).obj (Over.mk xbar.hom) ≅ Over.mk (xbar.hom ≫ f) :=
  Over.isoMk (Iso.refl _) (Category.id_comp _)

/-- Spaces étale pullback composed with the forgetful functor is ordinary over-category
pullback. -/
private noncomputable def smallEtaleInverseImage_pullbackForgetIso (V : spacesEtaleSite Y) :
    (CategoryTheory.Over.pullback f).obj
        ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V) ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V) :=
  (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f).symm.app V

/-- The fibre of the comap site-point of `x̄` along `f` maps to the fibre of `ȳ = f ∘ x̄`
by the inverse of `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberHom :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites
          (h_small := initiallySmall_of_essentiallySmall _) (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber ⟶
      (toSpacesEtalePoint (xbar.map f)).fiber where
  app V :=
    TypeCat.ofHom fun α ↦
      smallEtaleInverseImage_imageFiberFromOver f xbar V
        ((smallEtaleInverseImage_imageOverIso f xbar).inv ≫
          ((CategoryTheory.Over.mapPullbackAdj f).homEquiv (Over.mk xbar.hom)
              ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V)).symm
            (smallEtaleInverseImage_comapFiberAsOver f xbar V α ≫
              (smallEtaleInverseImage_pullbackForgetIso f V).inv))
  naturality := fun _ _ _ ↦ sorry

/-- The fibre of `ȳ = f ∘ x̄` maps to the fibre of the comap site-point of `x̄` along `f`
by `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberInv :
    (toSpacesEtalePoint (xbar.map f)).fiber ⟶
      (((toSpacesEtalePoint xbar).comapOfMorphismOfSites
          (h_small := initiallySmall_of_essentiallySmall _) (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber where
  app V :=
    TypeCat.ofHom fun β ↦
      smallEtaleInverseImage_comapFiberFromOver f xbar V
        (((CategoryTheory.Over.mapPullbackAdj f).homEquiv (Over.mk xbar.hom)
              ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V)
            ((smallEtaleInverseImage_imageOverIso f xbar).hom ≫
              smallEtaleInverseImage_imageFiberAsOver f xbar V β)) ≫
          (smallEtaleInverseImage_pullbackForgetIso f V).hom)
  naturality := fun _ _ _ ↦ sorry

end

/-- Comparison of the comap site-point fibre with the stalk at `ȳ = f ∘ x̄`. -/
noncomputable def smallEtaleInverseImage_comapStalkIso
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites
          (h_small := initiallySmall_of_essentiallySmall _) (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).sheafFiber.obj G ≅
      (toSpacesEtalePoint (xbar.map f)).sheafFiber.obj G := by
  refine
    { hom := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G
      inv := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- The forward map of the comap-to-image stalk comparison is induced by the
pullback-projection fibre map. -/
theorem smallEtaleInverseImage_comapStalkIso_hom
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_comapStalkIso f xbar G).hom =
      (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G :=
  rfl

/-- Canonical identification `(f_spaces,étale⁻¹ G')_x̄ ≅ G'_ȳ` for `ȳ = f ∘ x̄`. -/
noncomputable def smallEtaleInverseImage_spacesStalkIso
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (toSpacesEtalePoint xbar).sheafFiber.obj
        (((spacesEtalePullback f).sheafPullback (Type (u + 1))
          (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj G) ≅
      (toSpacesEtalePoint (xbar.map f)).sheafFiber.obj G :=
  ((toSpacesEtalePoint xbar).sheafFiberComapIsoOfMorphismOfSites
        (h_small := initiallySmall_of_essentiallySmall _)
        (spacesEtalePullback f) (Type (u + 1))).symm.app G ≪≫
    smallEtaleInverseImage_comapStalkIso f xbar G

/-- The stalk of small étale inverse image at a geometric point is canonically
isomorphic to the original small étale stalk at its image. -/
noncomputable def smallEtaleInverseImage_stalkIso
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (toSmallEtalePoint xbar).sheafFiber.obj
        ((smallEtaleMorphismOfTopoi f).inverseImage.obj G) ≅
      (toSmallEtalePoint (xbar.map f)).sheafFiber.obj G :=
  smallEtaleRestrictionStalkIso xbar
      (((spacesEtaleMorphismOfTopoi f).inverseImage).obj
        ((smallEtaleInclusionDirectImage Y).obj G)) ≪≫
    smallEtaleInverseImage_spacesStalkIso f xbar ((smallEtaleInclusionDirectImage Y).obj G) ≪≫
    (smallEtaleRestrictionStalkIso (xbar.map f)
      ((smallEtaleInclusionDirectImage Y).obj G)).symm ≪≫
    (toSmallEtalePoint (xbar.map f)).sheafFiber.mapIso
      ((smallEtalePresentationCounitIso Y).app G)

/-- The forward stalk map is the composite of restriction comparison, spaces-site
inverse-image comparison, reverse restriction comparison, and the presentation counit. -/
theorem smallEtaleInverseImage_stalkIso_hom
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_stalkIso f xbar G).hom =
      (smallEtaleRestrictionStalkIso xbar
        (((spacesEtaleMorphismOfTopoi f).inverseImage).obj
          ((smallEtaleInclusionDirectImage Y).obj G))).hom ≫
      (smallEtaleInverseImage_spacesStalkIso f xbar
        ((smallEtaleInclusionDirectImage Y).obj G)).hom ≫
      (smallEtaleRestrictionStalkIso (xbar.map f)
        ((smallEtaleInclusionDirectImage Y).obj G)).inv ≫
      (toSmallEtalePoint (xbar.map f)).sheafFiber.map
        ((smallEtalePresentationCounitIso Y).hom.app G) :=
  rfl

/-- The forward and reverse small étale stalk identifications compose to the identity. -/
theorem smallEtaleInverseImage_stalkIso_spec
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_stalkIso f xbar G).hom ≫
        (smallEtaleInverseImage_stalkIso f xbar G).inv =
      𝟙 _ :=
  (smallEtaleInverseImage_stalkIso f xbar G).hom_inv_id

end AlgebraicGeometry.AlgebraicSpace
