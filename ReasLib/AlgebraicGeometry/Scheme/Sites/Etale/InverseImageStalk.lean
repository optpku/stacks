/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

/-- Pullback of pointed étale neighborhoods is identified with neighborhoods
of the image point by the usual slice adjunction. Both maps are supplied by
that adjunction, without selecting an inverse from an invertibility assertion. -/
noncomputable def smallEtalePullback_fiberIso (K : Type u) [Field K]
    (point : Spec (.of K) ⟶ X) :
    smallEtalePullback f ⋙
        (Etale.forget X ⋙ coyoneda.obj (Opposite.op (Over.mk point))) ≅
      Etale.forget Y ⋙ coyoneda.obj (Opposite.op (Over.mk (point ≫ f))) :=
  Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f)
      (coyoneda.obj (Opposite.op (Over.mk point))) ≪≫
    Functor.isoWhiskerLeft (Etale.forget Y)
      (((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app
        (Opposite.op (Over.mk point))).symm)

private def fiberElementsEquivalence {C : Type*} [Category C]
    {F G : C ⥤ Type u} (e : F ≅ G) : F.Elements ≌ G.Elements where
  functor := e.hom.mapElements
  inverse := e.inv.mapElements
  unitIso := NatIso.ofComponents
    (fun x => CategoryOfElements.isoMk _ _ (Iso.refl _) (by
      change (F.map (𝟙 x.1)) x.2 = e.inv.app _ (e.hom.app _ x.2)
      simpa using ((e.app _).toEquiv.left_inv x.2).symm))
    (by rintro ⟨_, _⟩ ⟨_, _⟩ ⟨g, hg⟩; ext; change g ≫ 𝟙 _ = 𝟙 _ ≫ g; simp only [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents
    (fun x => CategoryOfElements.isoMk _ _ (Iso.refl _) (by
      change (G.map (𝟙 x.1)) (e.hom.app _ (e.inv.app _ x.2)) = x.2
      simpa using (e.app _).toEquiv.right_inv x.2))
    (by rintro ⟨_, _⟩ ⟨_, _⟩ ⟨g, hg⟩; ext; change g ≫ 𝟙 _ = 𝟙 _ ≫ g; simp only [Category.comp_id, Category.id_comp])
  functor_unitIso_comp x := by
    apply CategoryOfElements.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The category of étale neighborhoods pulled back along a scheme morphism and lifted
from a field-valued point is initially small. -/
theorem smallEtalePullback_fiber_initiallySmall (K : Type u) [Field K]
    (point : Spec (.of K) ⟶ X) :
    InitiallySmall.{u}
      ((smallEtalePullback f ⋙
        (Etale.forget X ⋙ coyoneda.obj (Opposite.op (Over.mk point)))).Elements) := by
  let s := point ≫ f
  let F := Etale.forget Y ⋙ coyoneda.obj (Opposite.op (Over.mk s))
  haveI : InitiallySmall.{u} F.Elements :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec Y) F).essImage (by
        rintro ⟨V, x⟩
        cases V with | _ W g
        obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
        change Spec (.of K) ⟶ W at y
        change y ≫ g = s at hy
        obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ W)
            (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
          obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
            (x := y.base default) (U := ⊤) (by simp)
          refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
          rintro _ ⟨a, rfl⟩
          rwa [Subsingleton.elim a default]
        exact ⟨_,
          ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ g)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
          ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩)
  exact initiallySmall_of_initial_of_initiallySmall
    (fiberElementsEquivalence (smallEtalePullback_fiberIso f K point)).inverse

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
          (smallEtaleInverseImage_imagePoint f xbar)).fiber :=
  (smallEtalePullback_fiberIso f xbar.K xbar.hom).hom

/-- The fibre of `ȳ = f ∘ x̄` maps to the fibre of the comap site-point of `x̄` along `f`
by `CategoryTheory.Over.mapPullbackAdj`. -/
noncomputable def smallEtaleInverseImage_comapFiberInv :
    (GeometricPoint.toSmallEtalePoint
          (smallEtaleInverseImage_imagePoint f xbar)).fiber ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
          (J := Y.smallEtaleTopology)
          (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
          (smallEtalePullback f)).fiber :=
  (smallEtalePullback_fiberIso f xbar.K xbar.hom).inv

/-- The composite of the forward and reverse comap-to-image stalk maps is the identity
on the stalk at the comapped point. -/
theorem smallEtaleInverseImage_comapStalk_hom_inv_id
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G ≫
      (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G =
        𝟙 _ := by
  let a : (GeometricPoint.toSmallEtalePoint
      (smallEtaleInverseImage_imagePoint f xbar)) ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f)) := ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩
  let b : ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
      (smallEtalePullback f)) ⟶ (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)) :=
    ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩
  have hab : b ≫ a = 𝟙 _ := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (smallEtalePullback_fiberIso f xbar.K xbar.hom).hom_inv_id
  exact congrArg (fun t => t.app G) ((Hom.sheafFiber_comp b a).symm.trans
    (by rw [hab, Hom.sheafFiber_id]))

/-- The composite of the reverse and forward comap-to-image stalk maps is the identity
on the stalk at the image geometric point. -/
theorem smallEtaleInverseImage_comapStalk_inv_hom_id
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩).app G ≫
      (Hom.sheafFiber (A := Type u) ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G =
        𝟙 _ := by
  let a : (GeometricPoint.toSmallEtalePoint
      (smallEtaleInverseImage_imagePoint f xbar)) ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f)) := ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩
  let b : ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
      (smallEtalePullback f)) ⟶ (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)) :=
    ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩
  have hab : a ≫ b = 𝟙 _ := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (smallEtalePullback_fiberIso f xbar.K xbar.hom).inv_hom_id
  exact congrArg (fun t => t.app G) ((Hom.sheafFiber_comp a b).symm.trans
    (by rw [hab, Hom.sheafFiber_id]))

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
        ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩).app G element := rfl

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
          (smallEtaleInverseImage_comapStalkIso f xbar G).hom := rfl

/-- The pointed-neighbourhood comparison works in any coefficient category
with the required colimits. Both directions are induced by the slice adjunction. -/
noncomputable def smallEtaleInverseImage_comapStalkIsoWithCoefficients
    (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A]
    (G : Sheaf Y.smallEtaleTopology A) :
    ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f)).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G := by
  let a : (GeometricPoint.toSmallEtalePoint
      (smallEtaleInverseImage_imagePoint f xbar)) ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
        (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
        (smallEtalePullback f)) := ⟨smallEtaleInverseImage_comapFiberHom f xbar⟩
  let b : ((GeometricPoint.toSmallEtalePoint xbar).comapOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
      (smallEtalePullback f)) ⟶ (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)) :=
    ⟨smallEtaleInverseImage_comapFiberInv f xbar⟩
  have hab : b ≫ a = 𝟙 _ := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (smallEtalePullback_fiberIso f xbar.K xbar.hom).hom_inv_id
  have hba : a ≫ b = 𝟙 _ := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (smallEtalePullback_fiberIso f xbar.K xbar.hom).inv_hom_id
  exact
    { hom := a.sheafFiber.app G
      inv := b.sheafFiber.app G
      hom_inv_id := by
        have h := congrArg (fun t => t.app G) ((Hom.sheafFiber_comp (A := A) b a).symm.trans
          (by rw [hab, Hom.sheafFiber_id]))
        exact h
      inv_hom_id := by
        have h := congrArg (fun t => t.app G) ((Hom.sheafFiber_comp (A := A) a b).symm.trans
          (by rw [hba, Hom.sheafFiber_id]))
        exact h }

/-- Inverse-image stalk comparison with arbitrary coefficients, in particular
modules. The comap comparison is mathlib's adjunction comparison. -/
noncomputable def smallEtaleInverseImage_stalkIsoWithCoefficients
    (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
    [HasWeakSheafify X.smallEtaleTopology A]
    [∀ P : Y.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology A) :
    (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
      (((smallEtalePullback f).sheafPullback A
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) ≅
      (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G :=
  ((GeometricPoint.toSmallEtalePoint xbar).sheafFiberComapIsoOfMorphismOfSites
    (h_small := smallEtalePullback_fiber_initiallySmall f xbar.K xbar.hom)
    (smallEtalePullback f) A).symm.app G ≪≫
      smallEtaleInverseImage_comapStalkIsoWithCoefficients f xbar A G

end AlgebraicGeometry.Scheme
