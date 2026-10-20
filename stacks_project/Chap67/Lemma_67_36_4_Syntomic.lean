/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Syntomic morphisms of algebraic spaces

A morphism of algebraic spaces is syntomic when every étale scheme square over
it has syntomic top arrow, in the sense of Stacks Definition 67.36.1 (1).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.syntomic_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Syntomic f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Syntomic h.left)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b), AlgebraicGeometry.Syntomic h.left)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, Syntomic (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.SyntomicAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.syntomicAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    SyntomicAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Syntomic (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.baseChangeOnSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.baseChangeOnAffineSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.existsSurjectiveEtaleSource :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.forallEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.existsEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.existsZariskiCover :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

end AlgebraicGeometry.AlgebraicSpace
