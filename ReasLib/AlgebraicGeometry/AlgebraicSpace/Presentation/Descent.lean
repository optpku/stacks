/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Descent along presentations of algebraic spaces

A morphism from a presenting scheme that equalizes the relation descends by sheaf
amalgamation along the atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Presentation

private def homDescLocalFamily {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    {V : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj V) :
    Presieve.FamilyOfElements Y.functorOfPoints (Presheaf.imageSieve P.atlas x).arrows :=
  fun W f hf => g.app (op W) (Presheaf.localPreimage P.atlas x f hf)

private theorem homDesc_eq_of_atlas_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V : Over S} (a b : V ⟶ P.U)
    (hab : P.atlas.app (op V) a = P.atlas.app (op V) b) :
    g.app (op V) a = g.app (op V) b := by
  have hw : yoneda.map a ≫ P.atlas = yoneda.map b ≫ P.atlas := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hab
  let r := Yoneda.fullyFaithful.preimage
    (P.isKernelPair.lift (yoneda.map a) (yoneda.map b) hw)
  have ht : r ≫ P.R.t = a := by
    apply yoneda.map_injective
    simp [r]
  have hs : r ≫ P.R.s = b := by
    apply yoneda.map_injective
    simp [r]
  have hh := ConcreteCategory.congr_hom (congr_app h (op V)) r
  change g.app (op V) (r ≫ P.R.t) = g.app (op V) (r ≫ P.R.s) at hh
  simpa only [ht, hs] using hh

private theorem homDescLocalFamily_compatible {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj V) :
    (homDescLocalFamily P g x).Compatible :=
  by
    intro V₁ V₂ W a b f₁ f₂ hf₁ hf₂ hab
    dsimp only [homDescLocalFamily]
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    apply homDesc_eq_of_atlas_eq P g h
    change P.atlas.app (op W)
        ((yoneda.obj P.U).map a.op (Presheaf.localPreimage P.atlas x f₁ hf₁)) =
      P.atlas.app (op W)
        ((yoneda.obj P.U).map b.op (Presheaf.localPreimage P.atlas x f₂ hf₂))
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
      Presheaf.app_localPreimage, Presheaf.app_localPreimage]
    simpa only [← Functor.map_comp_apply, ← op_comp] using
      congrArg (fun k => X.functorOfPoints.map k.op x) hab

private def homDescApp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    (V : (Over S)ᵒᵖ) (x : X.functorOfPoints.obj V) : Y.functorOfPoints.obj V :=
  let comparison : Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
    Scheme.grothendieckTopology_monotone (fun _ _ i _ ↦
      ⟨inferInstanceAs (AlgebraicGeometry.Flat i),
        inferInstanceAs (AlgebraicGeometry.LocallyOfFinitePresentation i)⟩)
  let covering : Presheaf.imageSieve P.atlas x ∈ (Scheme.fppfTopology.over S) V.unop :=
    comparison _ (P.atlas_locallySurjective.imageSieve_mem x)
  let sheaf := (isSheaf_iff_isSheaf_of_type _ _).1 Y.isSheaf _ covering
  sheaf.amalgamate (homDescLocalFamily P g x) (homDescLocalFamily_compatible P g h x)

private theorem homDescApp_map_of_lift {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj V)
    {W : Over S} (f : W ⟶ V.unop) (a : W ⟶ P.U)
    (ha : P.atlas.app (op W) a = X.functorOfPoints.map f.op x) :
    Y.functorOfPoints.map f.op (homDescApp P g h V x) = g.app (op W) a := by
  have hf : Presheaf.imageSieve P.atlas x f := ⟨a, ha⟩
  have hglue : Y.functorOfPoints.map f.op (homDescApp P g h V x) =
      homDescLocalFamily P g x f hf := by
    unfold homDescApp
    exact Presieve.IsSheafFor.valid_glue _ _ _ _
  refine hglue.trans ?_
  apply homDesc_eq_of_atlas_eq P g h
  exact (Presheaf.app_localPreimage P.atlas x f hf).trans ha.symm

private theorem homDescApp_naturality {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V W : (Over S)ᵒᵖ} (f : V ⟶ W) :
    X.functorOfPoints.map f ≫ TypeCat.ofHom (homDescApp P g h W) =
      TypeCat.ofHom (homDescApp P g h V) ≫ Y.functorOfPoints.map f :=
  by
    apply ConcreteCategory.hom_ext
    intro x
    let comparison : Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
      Scheme.grothendieckTopology_monotone (fun _ _ i _ ↦
        ⟨inferInstanceAs (AlgebraicGeometry.Flat i),
          inferInstanceAs (AlgebraicGeometry.LocallyOfFinitePresentation i)⟩)
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Y.isSheaf).isSeparated _
      (comparison _ (P.atlas_locallySurjective.imageSieve_mem
        (X.functorOfPoints.map f x)))).ext
    rintro Z a ⟨b, hb⟩
    change Y.functorOfPoints.map a.op (homDescApp P g h W (X.functorOfPoints.map f x)) =
      Y.functorOfPoints.map a.op (Y.functorOfPoints.map f (homDescApp P g h V x))
    have hb' : P.atlas.app (op Z) b =
        X.functorOfPoints.map (a ≫ f.unop).op x := by
      simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
        ConcreteCategory.comp_apply] using hb
    calc
      _ = g.app (op Z) b := homDescApp_map_of_lift P g h _ a b hb
      _ = _ := by
        simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
          ConcreteCategory.comp_apply] using
          (homDescApp_map_of_lift P g h x (a ≫ f.unop) b hb').symm

/-- A morphism from a presenting scheme that equalizes the relation descends uniquely
to a morphism of algebraic spaces. -/
@[no_expose] def homDesc {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) : X ⟶ Y where
  app V := TypeCat.ofHom (homDescApp P g h V)
  naturality := fun _ _ f => homDescApp_naturality P g h f

/-- Precomposing a descended morphism with the atlas recovers the given morphism
from the presenting scheme. -/
theorem homDesc_comp_atlas {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    P.atlas ≫ homDesc P g h = (g : yoneda.obj P.U ⟶ Y.functorOfPoints) :=
  by
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro a
    change homDescApp P g h V (P.atlas.app V a) = g.app V a
    have ha : P.atlas.app (op V.unop) a =
        X.functorOfPoints.map (𝟙 V.unop).op (P.atlas.app V a) := by
      simp
    have hc : Y.functorOfPoints.map (𝟙 V)
        (homDescApp P g h V (P.atlas.app V a)) = g.app V a :=
      homDescApp_map_of_lift P g h (P.atlas.app V a) (𝟙 V.unop) a ha
    exact (Y.functorOfPoints.map_id_apply V _).symm.trans hc

end AlgebraicGeometry.AlgebraicSpace.Presentation
