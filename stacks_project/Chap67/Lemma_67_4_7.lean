/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Section

/-!
# Sections of morphisms of algebraic spaces

A section of a morphism of algebraic spaces over a scheme is representable,
locally of finite type, locally quasi-finite, separated, and a monomorphism in
the sense of Definition 65.5.1. If the morphism is locally separated then the
section is an immersion; if it is separated then the section is a closed
immersion; if it is quasi-separated then the section is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 67.4.7 (1): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. Then `s`
is representable. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T),
      yoneda.relativelyRepresentable s)

/- Lemma 67.4.7 (2): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. Then `s`
is locally of finite type in the sense of Definition 65.5.1. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T),
      (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
          MorphismProperty Scheme.{u})).presheaf s)

/- Lemma 67.4.7 (3): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. Then `s`
is locally quasi-finite in the sense of Definition 65.5.1. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T),
      (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf s)

/- Lemma 67.4.7 (4): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. Then `s`
is separated in the sense of Definition 65.5.1. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.isSeparated_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T),
      (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
          MorphismProperty Scheme.{u})).presheaf s)

/- Lemma 67.4.7 (5): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. Then `s`
is a monomorphism in the sense of Definition 65.5.1. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.monomorphisms_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T),
      (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf s)

/- Lemma 67.4.7 (6): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. If `f` is
locally separated, then `s` is an immersion. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T)
      [AlgebraicGeometry.AlgebraicSpace.LocallySeparated f],
      AlgebraicGeometry.AlgebraicSpace.IsImmersion s)

/- Lemma 67.4.7 (7): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. If `f` is
separated, then `s` is a closed immersion. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T)
      [AlgebraicGeometry.AlgebraicSpace.Separated f],
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion s)

/- Lemma 67.4.7 (8): let `S` be a scheme, let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`, and let `s : T ⟶ X` be a section of `f`. If `f` is
quasi-separated, then `s` is quasi-compact in the sense of Definition 65.5.1. -/
@[stacks 03KP]
#check (AlgebraicGeometry.AlgebraicSpace.quasiCompact_section :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
      (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T)
      [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f],
      (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
          MorphismProperty Scheme.{u})).presheaf s)
