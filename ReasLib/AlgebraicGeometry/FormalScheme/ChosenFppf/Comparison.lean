/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Points
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.ChosenFppf.Points

/-!
# Comparison of EGA and McQuillan points sheaves
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

/-- Yoneda embedding of `ofFormalScheme` on morphisms into an EGA formal scheme. -/
def ofFormalSchemeYoneda (X : FormalScheme.{u}) :
    yoneda.obj X ⟶
      McQuillan.FormalScheme.ofFormalScheme.op ⋙
        yoneda.obj (McQuillan.FormalScheme.ofFormalScheme.obj X) :=
  yonedaMap McQuillan.FormalScheme.ofFormalScheme X

/-- Inverse of `ofFormalSchemeYoneda` on underlying LTRS morphisms. -/
def ofFormalSchemeYonedaInv (X : FormalScheme.{u}) :
    McQuillan.FormalScheme.ofFormalScheme.op ⋙
        yoneda.obj (McQuillan.FormalScheme.ofFormalScheme.obj X) ⟶
      yoneda.obj X where
  app Y :=
    TypeCat.ofHom fun
      (f : McQuillan.FormalScheme.ofFormalScheme.obj (unop Y) ⟶
        McQuillan.FormalScheme.ofFormalScheme.obj X) ↦
      (Hom.ofLTRSHom (McQuillan.FormalScheme.Hom.toLTRSHom f) : unop Y ⟶ X)
  naturality := sorry

/-- Components of `ofFormalSchemeYoneda` are `ofFormalScheme.map`. -/
theorem ofFormalSchemeYoneda_app (X : FormalScheme.{u})
    {Y : FormalScheme.{u}} (f : Y ⟶ X) :
    (ofFormalSchemeYoneda X).app (op Y) f =
      McQuillan.FormalScheme.ofFormalScheme.map f :=
  rfl

/-- The morphism of functors of points induced by `ofFormalScheme`. -/
def sheafOfPointsCompareHom (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    (sheafOfPoints 𝒮 S).obj X ⟶
      (McQuillan.FormalScheme.sheafOfPoints 𝒮 S).obj
        (McQuillan.FormalScheme.ofFormalScheme.obj X) :=
  ObjectProperty.homMk
    (whiskerRight
      (whiskerLeft ((𝒮.bigToScheme S).op ⋙ Scheme.toFormalScheme.op)
        (ofFormalSchemeYoneda X))
      uliftFunctor.{v})

/-- The inverse morphism of functors of points, on underlying LTRS morphisms. -/
def sheafOfPointsCompareInv (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    (McQuillan.FormalScheme.sheafOfPoints 𝒮 S).obj
        (McQuillan.FormalScheme.ofFormalScheme.obj X) ⟶
      (sheafOfPoints 𝒮 S).obj X :=
  ObjectProperty.homMk
    (whiskerRight
      (whiskerLeft ((𝒮.bigToScheme S).op ⋙ Scheme.toFormalScheme.op)
        (ofFormalSchemeYonedaInv X))
      uliftFunctor.{v})

/-- The canonical comparison morphisms of points sheaves are inverse to each other. -/
theorem sheafOfPointsCompare_laws (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    sheafOfPointsCompareHom 𝒮 S X ≫ sheafOfPointsCompareInv 𝒮 S X =
        𝟙 ((sheafOfPoints 𝒮 S).obj X) ∧
      sheafOfPointsCompareInv 𝒮 S X ≫ sheafOfPointsCompareHom 𝒮 S X =
        𝟙 ((McQuillan.FormalScheme.sheafOfPoints 𝒮 S).obj
          (McQuillan.FormalScheme.ofFormalScheme.obj X)) :=
  sorry

/-- The functors of points of an EGA formal scheme and of its McQuillan
embedding are canonically isomorphic on a chosen big fppf site. -/
def sheafOfPointsCompare (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    (sheafOfPoints 𝒮 S).obj X ≅
      (McQuillan.FormalScheme.sheafOfPoints 𝒮 S).obj
        (McQuillan.FormalScheme.ofFormalScheme.obj X) where
  hom := sheafOfPointsCompareHom 𝒮 S X
  inv := sheafOfPointsCompareInv 𝒮 S X
  hom_inv_id := (sheafOfPointsCompare_laws 𝒮 S X).1
  inv_hom_id := (sheafOfPointsCompare_laws 𝒮 S X).2

/-- Components of `sheafOfPointsCompare` are `ofFormalScheme.map` on Hom-spaces. -/
theorem sheafOfPointsCompare_app (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) (T : (𝒮.bigSite S)ᵒᵖ)
    (f : Scheme.toFormalScheme.obj ((𝒮.bigToScheme S).obj T.unop) ⟶ X) :
    ((sheafOfPointsCompare 𝒮 S X).hom.hom.app T ⟨f⟩).down =
      McQuillan.FormalScheme.ofFormalScheme.map f :=
  rfl

end AlgebraicGeometry.FormalScheme
