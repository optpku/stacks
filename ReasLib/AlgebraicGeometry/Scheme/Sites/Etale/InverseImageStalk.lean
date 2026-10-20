module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Point.Category

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.Point

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The category of étale neighborhoods pulled back along a scheme morphism and lifted
from a field-valued point is initially small. -/
theorem smallEtalePullback_fiber_initiallySmall (K : Type u) [Field K]
    (point : Spec (.of K) ⟶ X) :
    InitiallySmall.{u}
      ((smallEtalePullback f ⋙
        (Etale.forget X ⋙ coyoneda.obj (Opposite.op (Over.mk point)))).Elements) := sorry

variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable (xbar : GeometricPoint X)

/-- The geometric point `ȳ = f ∘ x̄` of `Y`. -/
noncomputable def smallEtaleInverseImage_imagePoint :
    GeometricPoint Y :=
  @GeometricPoint.of Y xbar.K inferInstance xbar.isAlgClosed (xbar.hom ≫ f)

/-- The fibre of the comap site-point of `x̄` along `f` maps to the fibre of `ȳ = f ∘ x̄`
by the inverse of `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberHom :
    ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
          (J := Y.smallEtaleTopology)
          (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
          (smallEtalePullback f)).fiber ⟶
      (GeometricPoint.toSmallEtalePoint
          (smallEtaleInverseImage_imagePoint f xbar)).fiber where
  app V :=
    TypeCat.ofHom fun lift =>
      let comparison :=
        (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f).app V
      let imageComparison :
          (CategoryTheory.Over.map f).obj (Over.mk xbar.hom) ≅ Over.mk (xbar.hom ≫ f) :=
        Over.isoMk (Iso.refl _) (Category.id_comp _)
      imageComparison.inv ≫
        ((CategoryTheory.Over.mapPullbackAdj f).homEquiv
          (Over.mk xbar.hom) ((Etale.forget Y).obj V)).symm
          ((lift : Over.mk xbar.hom ⟶
            (Etale.forget X).obj ((smallEtalePullback f).obj V)) ≫ comparison.hom)
  naturality := fun _ _ _ => sorry

/-- The fibre of `ȳ = f ∘ x̄` maps to the fibre of the comap site-point of `x̄` along `f`
by `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberInv :
    (GeometricPoint.toSmallEtalePoint
          (smallEtaleInverseImage_imagePoint f xbar)).fiber ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
          (J := Y.smallEtaleTopology)
          (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
          (smallEtalePullback f)).fiber where
  app V :=
    TypeCat.ofHom fun lift =>
      let comparison :=
        (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f).app V
      let imageComparison :
          (CategoryTheory.Over.map f).obj (Over.mk xbar.hom) ≅ Over.mk (xbar.hom ≫ f) :=
        Over.isoMk (Iso.refl _) (Category.id_comp _)
      ((CategoryTheory.Over.mapPullbackAdj f).homEquiv
        (Over.mk xbar.hom) ((Etale.forget Y).obj V)
        (imageComparison.hom ≫
          (lift : Over.mk (xbar.hom ≫ f) ⟶ (Etale.forget Y).obj V))) ≫ comparison.inv
  naturality := fun _ _ _ => sorry

/-- The composite of the forward and reverse comap-to-image stalk maps is the identity
on the stalk at the comapped point. -/
theorem smallEtaleInverseImage_comapStalk_hom_inv_id
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G ≫
      (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G =
        𝟙 _ := sorry

/-- The composite of the reverse and forward comap-to-image stalk maps is the identity
on the stalk at the image geometric point. -/
theorem smallEtaleInverseImage_comapStalk_inv_hom_id
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G ≫
      (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G =
        𝟙 _ := sorry

/-- The stalk at the comapped site point is canonically isomorphic to the stalk at
the image geometric point. -/
noncomputable def smallEtaleInverseImage_comapStalkIso
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f)).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G where
  hom := (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G
  inv := (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G
  hom_inv_id := smallEtaleInverseImage_comapStalk_hom_inv_id f xbar G
  inv_hom_id := smallEtaleInverseImage_comapStalk_inv_hom_id f xbar G

/-- The forward comap-to-image stalk comparison is induced by the forward fiber map. -/
theorem smallEtaleInverseImage_comapStalkIso_hom_apply
    (G : Sheaf Y.smallEtaleTopology (Type u))
    (element : ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
      (smallEtalePullback f)).sheafFiber.obj G) :
    (smallEtaleInverseImage_comapStalkIso f xbar G).hom element =
      (Hom.sheafFiber (A := Type u)
        ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G element := sorry

/-- The stalk of inverse image at a geometric point is canonically isomorphic to the
original sheaf's stalk at the image geometric point. -/
noncomputable def smallEtaleInverseImage_stalkIso
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
      (((smallEtalePullback f).sheafPullback (Type u)
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) ≅
      (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G :=
  ((GeometricPoint.toSmallEtalePoint xbar).sheafFiberComapIsoOfMorphismOfSites
    (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
    (smallEtalePullback f) (Type u)).symm.app G ≪≫
      smallEtaleInverseImage_comapStalkIso f xbar G

/-- The forward stalk comparison is the inverse comap comparison followed by the
comap-to-image stalk comparison. -/
theorem smallEtaleInverseImage_stalkIso_hom
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (smallEtaleInverseImage_stalkIso f xbar G).hom =
      ((GeometricPoint.toSmallEtalePoint xbar).sheafFiberComapIsoOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f) (Type u)).inv.app G ≫
          (smallEtaleInverseImage_comapStalkIso f xbar G).hom := sorry

end AlgebraicGeometry.Scheme
