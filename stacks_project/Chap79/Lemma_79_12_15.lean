/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.SectionInclusion

/-! # Finite open families containing a section -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/- Lemma 79.12.15. Let S be a scheme, f : X ⟶ Y a morphism of algebraic spaces
 over S, and σ : Y ⟶ X a section of f. The transformation
 t : (X/Y, σ)_fin ⟶ (X/Y)_fin forgetting that the finite open family contains
 the section is representable by open immersions. If f is separated, it is
 representable by open and closed immersions. If (X/Y)_fin is an algebraic space,
 then (X/Y, σ)_fin is an algebraic space and an open subspace of it. If (X/Y)_fin
 is a scheme, then (X/Y, σ)_fin is an open subscheme of it. -/
@[stacks 04RR] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionι_isOpenImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    (MorphismProperty.over
        (@AlgebraicGeometry.IsOpenImmersion :
          MorphismProperty Scheme.{u})).presheaf
      (withSectionι f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionι_isOpenAndClosedImmersion :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y),
    (MorphismProperty.over
        ((@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf
      (withSectionι f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsAlgebraicSpace_withSectionFunctor :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    IsAlgebraicSpace (withSectionFunctor f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionιHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y),
    ofIsAlgebraicSpace (withSectionFunctor f σ hσ) ⟶
      ofIsAlgebraicSpace (functor f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsOpenImmersion_withSectionι :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    AlgebraicSpace.IsOpenImmersion (withSectionιHom f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionOpenSubspace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y →
    OpenSubspace (ofIsAlgebraicSpace (functor f)))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionOpenSubspace_X :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y),
    (withSectionOpenSubspace f σ hσ).X =
      ofIsAlgebraicSpace (withSectionFunctor f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionOpenSubspace_ι :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y),
    (withSectionOpenSubspace f σ hσ).ι = withSectionιHom f σ hσ)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsRepresentable_withSectionFunctor :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Functor.IsRepresentable (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y),
    Functor.IsRepresentable (withSectionFunctor f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.exists_isOpenImmersion_of_isRepresentable :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T : Over S} (e : yoneda.obj T ≅ functor f),
    ∃ (T' : Over S) (ι : T' ⟶ T)
      (e' : yoneda.obj T' ≅ withSectionFunctor f σ hσ),
      AlgebraicGeometry.IsOpenImmersion ι.left ∧
        yoneda.map ι ≫ e.hom = e'.hom ≫ withSectionι f σ hσ)

end AlgebraicGeometry.AlgebraicSpace.FinitePart
