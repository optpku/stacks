/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection

/-!
# Inclusion of finite open families containing a section

Forgetting the section condition gives an open immersion of finite-part presheaves,
and a simultaneous open and closed immersion when the original morphism is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

private def withSectionιApp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (T : (Over S)ᵒᵖ) :
    (withSectionFunctor f σ hσ).obj T ⟶ (functor f).obj T :=
  TypeCat.ofHom fun p ↦
    (functor_obj_equiv f T.unop).symm
      (PointQuot.mk (((withSectionFunctor_obj_equiv f σ hσ T.unop) p).toPoint.toSubspacePoint))

private theorem withSectionι_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (withSectionFunctor f σ hσ).map h ≫ withSectionιApp f σ hσ T' =
      withSectionιApp f σ hσ T ≫ (functor f).map h := sorry

/-- The forgetful transformation sends a finite open family containing the section
to its underlying finite open family. -/
@[no_expose]
def withSectionι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    withSectionFunctor f σ hσ ⟶ functor f where
  app := withSectionιApp f σ hσ
  naturality {_ _} h := withSectionι_naturality f σ hσ h

/-- Each component of the forgetful transformation takes the subspace class of
the underlying finite open family. -/
theorem withSectionι_app {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : (Over S)ᵒᵖ) (p : (withSectionFunctor f σ hσ).obj T) :
    (withSectionι f σ hσ).app T p =
      (functor_obj_equiv f T.unop).symm
        (PointQuot.mk (((withSectionFunctor_obj_equiv f σ hσ T.unop) p).toPoint.toSubspacePoint)) :=
  by rfl

/-- On a with-section pair, the forgetful transformation retains exactly the
underlying open-subspace class. -/
theorem withSectionι_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T : Over S} (p : WithSection.Point f σ hσ T) :
    (withSectionι f σ hσ).app (op T)
        ((withSectionFunctor_obj_equiv f σ hσ T).symm p) =
      (functor_obj_equiv f T).symm (PointQuot.mk p.toPoint.toSubspacePoint) := by
  rw [withSectionι_app, Equiv.apply_symm_apply]

/-- For any morphism of algebraic spaces with a specified section, forgetting the
section condition on finite open families is representable by open immersions. -/
theorem withSectionι_isOpenImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (MorphismProperty.over
        (@AlgebraicGeometry.IsOpenImmersion :
          MorphismProperty Scheme.{u})).presheaf
      (withSectionι f σ hσ) :=
  sorry

/-- For a separated morphism of algebraic spaces with a specified section, forgetting
the section condition on finite open families is representable by open and closed immersions. -/
theorem withSectionι_isOpenAndClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (MorphismProperty.over
        ((@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf
      (withSectionι f σ hσ) :=
  sorry

/-- If `(X/Y)_fin` is an algebraic space, then so is `(X/Y, σ)_fin`. -/
instance instIsAlgebraicSpace_withSectionFunctor {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    IsAlgebraicSpace (withSectionFunctor f σ hσ) :=
  sorry

/-- The inclusion `t` as a morphism of algebraic spaces, when both functors are
algebraic spaces. -/
def withSectionιHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    ofIsAlgebraicSpace (withSectionFunctor f σ hσ) ⟶
      ofIsAlgebraicSpace (functor f) :=
  withSectionι f σ hσ

/-- If `(X/Y)_fin` is an algebraic space, then `t` is an open immersion of
algebraic spaces. -/
instance instIsOpenImmersion_withSectionι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    AlgebraicSpace.IsOpenImmersion (withSectionιHom f σ hσ) :=
  sorry

/-- If the finite-part presheaf is an algebraic space, finite open families containing
the specified section form an open subspace of it. -/
def withSectionOpenSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    OpenSubspace (ofIsAlgebraicSpace (functor f)) :=
  OpenSubspace.ofι (withSectionιHom f σ hσ)

/-- The underlying algebraic space of the open subspace is `(X/Y, σ)_fin`. -/
theorem withSectionOpenSubspace_X {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionOpenSubspace f σ hσ).X =
      ofIsAlgebraicSpace (withSectionFunctor f σ hσ) :=
  rfl

/-- The inclusion of the open subspace is `withSectionιHom`. -/
theorem withSectionOpenSubspace_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionOpenSubspace f σ hσ).ι = withSectionιHom f σ hσ :=
  rfl

/-- If `(X/Y)_fin` is representable, then so is `(X/Y, σ)_fin`. -/
instance instIsRepresentable_withSectionFunctor {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Functor.IsRepresentable (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    Functor.IsRepresentable (withSectionFunctor f σ hσ) :=
  sorry

/-- For any scheme representing the finite-part presheaf, the presheaf of finite open
families containing the specified section is represented by an open subscheme, with
the forgetful transformation induced by the open immersion. -/
theorem exists_isOpenImmersion_of_isRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T : Over S} (e : yoneda.obj T ≅ functor f) :
    ∃ (T' : Over S) (ι : T' ⟶ T)
      (e' : yoneda.obj T' ≅ withSectionFunctor f σ hσ),
      AlgebraicGeometry.IsOpenImmersion ι.left ∧
        yoneda.map ι ≫ e.hom = e'.hom ≫ withSectionι f σ hσ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
