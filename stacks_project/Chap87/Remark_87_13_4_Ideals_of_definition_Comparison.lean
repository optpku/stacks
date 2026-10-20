/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_FormalScheme
public import stacks_project.Chap87.Remark_87_9_8_Comparison
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_System
public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_System

/-!
# EGA / McQuillan comparison for ideals of definition

EGA affine opens remain McQuillan affine opens after `ofFormalScheme`, ideal
sheaves restrict, and the functors of points of `X` and of
`ofFormalScheme.obj X` are isomorphic. On a quasi-compact EGA formal scheme,
existence of a fundamental system of ideals of definition is equivalent to
existence of a fundamental system of weak ideals of definition on the
McQuillan embedding.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open TopologicalSpace Topology AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/-- An EGA formal affine open remains a McQuillan formal affine open on the
image of `ofFormalScheme`. -/
theorem isAffineOpen_ofFormalScheme {X : FormalScheme.{u}} {U : Opens X.carrier}
    (hU : IsAffineOpen U) :
    @McQuillan.FormalScheme.IsAffineOpen
      (McQuillan.FormalScheme.ofFormalScheme.obj X) U :=
  sorry

/-- Restrict a McQuillan ideal sheaf on `ofFormalScheme.obj X` to EGA affine
opens of `X`. -/
def IdealSheafData.ofMcQuillan {X : FormalScheme.{u}}
    (I : McQuillan.FormalScheme.IdealSheafData
      (McQuillan.FormalScheme.ofFormalScheme.obj X)) :
    IdealSheafData X where
  ideal U :=
    I.ideal
      ⟨(U.1 : Opens (McQuillan.FormalScheme.ofFormalScheme.obj X).carrier),
        isAffineOpen_ofFormalScheme U.2⟩
  map_ideal := sorry

/-- On an EGA formal affine open, `ofMcQuillan` recovers the McQuillan
component. -/
theorem IdealSheafData.ofMcQuillan_ideal {X : FormalScheme.{u}}
    (I : McQuillan.FormalScheme.IdealSheafData
      (McQuillan.FormalScheme.ofFormalScheme.obj X))
    (U : X.affineOpens) :
    (IdealSheafData.ofMcQuillan I).ideal U =
      I.ideal
        ⟨(U.1 : Opens (McQuillan.FormalScheme.ofFormalScheme.obj X).carrier),
          isAffineOpen_ofFormalScheme U.2⟩ :=
  sorry

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
      (⟨f.toLTRSHom⟩ : unop Y ⟶ X)
  naturality := sorry

/-- Components of `ofFormalSchemeYoneda` are `ofFormalScheme.map`. -/
theorem ofFormalSchemeYoneda_app (X : FormalScheme.{u})
    {Y : FormalScheme.{u}} (f : Y ⟶ X) :
    (ofFormalSchemeYoneda X).app (op Y) f =
      McQuillan.FormalScheme.ofFormalScheme.map f :=
  sorry

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
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Components of `sheafOfPointsCompare` are `ofFormalScheme.map` on Hom-spaces. -/
theorem sheafOfPointsCompare_app (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) (T : (𝒮.bigSite S)ᵒᵖ)
    (f : Scheme.toFormalScheme.obj ((𝒮.bigToScheme S).obj T.unop) ⟶ X) :
    ((sheafOfPointsCompare 𝒮 S X).hom.hom.app T ⟨f⟩).down =
      McQuillan.FormalScheme.ofFormalScheme.map f :=
  sorry

/-- A quasi-compact EGA formal scheme admits a finite cover by formal affine
opens. -/
theorem exists_finite_affineOpen_cover (X : FormalScheme.{u})
    [CompactSpace X.carrier] :
    ∃ (n : ℕ) (𝒰 : Fin n → X.affineOpens), ⨆ i, (𝒰 i).1 = ⊤ :=
  sorry

/-- On a quasi-compact EGA formal scheme, a fundamental system of ideals of
definition exists if and only if the McQuillan embedding admits a fundamental
system of weak ideals of definition. -/
theorem exists_fundamentalSystem_iff_exists_weakFundamentalSystem
    {X : FormalScheme.{u}} [CompactSpace X.carrier] :
    Nonempty (FundamentalSystem X) ↔
      Nonempty
        (McQuillan.FormalScheme.FundamentalSystem
          (McQuillan.FormalScheme.ofFormalScheme.obj X)) :=
  sorry

end AlgebraicGeometry.FormalScheme
