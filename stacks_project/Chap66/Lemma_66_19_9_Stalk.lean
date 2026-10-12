/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import stacks_project.Chap66.Definition_66_19_2_EtaleNeighborhood
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_19_3_Cofiltered
public import stacks_project.Chap66.Lemma_66_19_7_Point

/-!
# Stalks of inverse images on étale sites of algebraic spaces

The stalk of `f_small⁻¹ G` at a geometric point `xbar` of `X` is canonically identified with
the stalk of `G` at `ybar = f ∘ xbar`. The comparison is obtained by comapping the spaces-étale
site point along `spacesEtalePullback`, then transporting along Lemma 66.18.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.Point

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/-- The category of étale neighborhoods of a geometric point of an algebraic space is initially
small in the universe of `etaleLiftFunctor`. -/
instance instInitiallySmall {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    InitiallySmall.{u + 1} (EtaleNeighborhood xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Covering sieves in the étale topology of algebraic spaces over `X` lift jointly
surjectively through `etaleLiftFunctor xbar`. -/
theorem coversLift_etaleLiftFunctor (xbar : GeometricPoint X) :
    GrothendieckTopology.Point.Fiber.coversLift (spacesEtaleTopology X)
      (etaleLiftFunctor xbar) :=
  sorry

/-- A geometric point of an algebraic space determines a point of the étale site of algebraic
spaces, whose fiber functor sends `U` to the type of lifts of the geometric point through
`U`. -/
noncomputable def toSpacesEtalePoint (xbar : GeometricPoint X) :
    (spacesEtaleTopology X).Point.{u + 1} where
  fiber := etaleLiftFunctor xbar
  jointly_surjective := sorry

/-- The fiber functor of `toSpacesEtalePoint xbar` is `etaleLiftFunctor xbar`. -/
theorem toSpacesEtalePoint_fiber (xbar : GeometricPoint X) :
    (toSpacesEtalePoint xbar).fiber = etaleLiftFunctor xbar :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (xbar : GeometricPoint X)
variable [InitiallySmall
  ((spacesEtalePullback f ⋙ (GeometricPoint.toSpacesEtalePoint xbar).fiber).Elements)]
variable [((spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
    (spacesEtaleTopology Y) (spacesEtaleTopology X)).IsRightAdjoint]

open GeometricPoint

/-- Underlying Over-morphism of a comap fibre element at `V`. -/
noncomputable def smallEtaleInverseImage_comapFiberAsOver
    (V : spacesEtaleSite Y)
    (α : (((toSpacesEtalePoint xbar).comapOfMorphismOfSites (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber.obj V) :
    Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V) :=
  α

/-- Underlying Over-morphism of a fibre element at `ȳ = f ∘ x̄` and `V`. -/
noncomputable def smallEtaleInverseImage_imageFiberAsOver
    (V : spacesEtaleSite Y)
    (β : (toSpacesEtalePoint (xbar.map f)).fiber.obj V) :
    Over.mk (xbar.hom ≫ f) ⟶ (MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V :=
  β

/-- Reverse ascription of `smallEtaleInverseImage_comapFiberAsOver`. -/
noncomputable def smallEtaleInverseImage_comapFiberFromOver
    (V : spacesEtaleSite Y)
    (α : Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V)) :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber.obj V :=
  α

/-- Reverse ascription of `smallEtaleInverseImage_imageFiberAsOver`. -/
noncomputable def smallEtaleInverseImage_imageFiberFromOver
    (V : spacesEtaleSite Y)
    (β : Over.mk (xbar.hom ≫ f) ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V) :
    (toSpacesEtalePoint (xbar.map f)).fiber.obj V :=
  β

/-- `Over.map f` applied to `Over.mk xbar.hom` is the over-object of `ȳ = f ∘ x̄`. -/
noncomputable def smallEtaleInverseImage_imageOverIso :
    (CategoryTheory.Over.map f).obj (Over.mk xbar.hom) ≅ Over.mk (xbar.hom ≫ f) :=
  Over.isoMk (Iso.refl _) sorry

/-- Spaces étale pullback composed with the forgetful functor is ordinary over-category
pullback. -/
noncomputable def smallEtaleInverseImage_pullbackForgetIso (V : spacesEtaleSite Y) :
    (CategoryTheory.Over.pullback f).obj
        ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V) ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((spacesEtalePullback f).obj V) :=
  (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f).symm.app V

/-- The fibre of the comap site-point of `x̄` along `f` maps to the fibre of `ȳ = f ∘ x̄`
by the inverse of `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberHom :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber ⟶
      (toSpacesEtalePoint (xbar.map f)).fiber where
  app V :=
    TypeCat.ofHom fun α ↦
      smallEtaleInverseImage_imageFiberFromOver f xbar V
        ((smallEtaleInverseImage_imageOverIso f xbar).inv ≫
          ((CategoryTheory.Over.mapPullbackAdj f).homEquiv (Over.mk xbar.hom)
              ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V)).symm
            (smallEtaleInverseImage_comapFiberAsOver f xbar V α))
  naturality := fun _ _ _ ↦ sorry

/-- The fibre of `ȳ = f ∘ x̄` maps to the fibre of the comap site-point of `x̄` along `f`
by `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberInv :
    (toSpacesEtalePoint (xbar.map f)).fiber ⟶
      (((toSpacesEtalePoint xbar).comapOfMorphismOfSites (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).fiber where
  app V :=
    TypeCat.ofHom fun β ↦
      smallEtaleInverseImage_comapFiberFromOver f xbar V
        (((CategoryTheory.Over.mapPullbackAdj f).homEquiv (Over.mk xbar.hom)
              ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).obj V)
            (smallEtaleInverseImage_imageFiberAsOver f xbar V β)) ≫
          (smallEtaleInverseImage_pullbackForgetIso f V).hom)
  naturality := fun _ _ _ ↦ sorry

/-- Comparison of the comap site-point fibre with the stalk at `ȳ = f ∘ x̄`. -/
noncomputable def smallEtaleInverseImage_comapStalkIso
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (((toSpacesEtalePoint xbar).comapOfMorphismOfSites (spacesEtalePullback f) :
            (spacesEtaleTopology Y).Point.{u + 1})).sheafFiber.obj G ≅
      (toSpacesEtalePoint (xbar.map f)).sheafFiber.obj G where
  hom := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G
  inv := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the comap-to-image stalk comparison is induced by the
pullback-projection fibre map. -/
theorem smallEtaleInverseImage_comapStalkIso_hom
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_comapStalkIso f xbar G).hom =
      (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G :=
  sorry

/-- Canonical identification `(f_spaces,étale⁻¹ G')_x̄ ≅ G'_ȳ` for `ȳ = f ∘ x̄`. -/
noncomputable def smallEtaleInverseImage_spacesStalkIso
    (G : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) :
    (toSpacesEtalePoint xbar).sheafFiber.obj
        (((spacesEtalePullback f).sheafPullback (Type (u + 1))
          (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj G) ≅
      (toSpacesEtalePoint (xbar.map f)).sheafFiber.obj G :=
  ((toSpacesEtalePoint xbar).sheafFiberComapIsoOfMorphismOfSites
        (spacesEtalePullback f) (Type (u + 1))).symm.app G ≪≫
    smallEtaleInverseImage_comapStalkIso f xbar G

/-- Canonical identification `(f_small⁻¹ G)_x̄ ≅ G_ȳ` for `ȳ = f ∘ x̄`, as the spaces-étale
stalk comparison of the Lemma 66.18.3 extension of `G`. -/
noncomputable def smallEtaleInverseImage_stalkIso
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (toSpacesEtalePoint xbar).sheafFiber.obj
        (((spacesEtalePullback f).sheafPullback (Type (u + 1))
          (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
        ((smallEtaleInclusionDirectImage Y).obj G)) ≅
      (toSpacesEtalePoint (xbar.map f)).sheafFiber.obj
        ((smallEtaleInclusionDirectImage Y).obj G) :=
  smallEtaleInverseImage_spacesStalkIso f xbar ((smallEtaleInclusionDirectImage Y).obj G)

/-- The forward map of the stalk identification is the inverse comap comparison composed with
the comap-to-image stalk comparison. -/
theorem smallEtaleInverseImage_stalkIso_hom
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_stalkIso f xbar G).hom =
      (smallEtaleInverseImage_spacesStalkIso f xbar
          ((smallEtaleInclusionDirectImage Y).obj G)).hom :=
  sorry

/-- The stalk identification compares the inverse-image stalk at `x̄` with the stalk of `G`
at `ȳ = f ∘ x̄`. -/
theorem smallEtaleInverseImage_stalkIso_spec
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    (smallEtaleInverseImage_stalkIso f xbar G).hom ≫
        (smallEtaleInverseImage_stalkIso f xbar G).inv =
      𝟙 _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
