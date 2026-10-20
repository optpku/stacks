/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Pair
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap67.Lemma_67_45_5_Pullback

/-!
# Finite parts of morphisms of algebraic spaces

A pair `(a, Z)` for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, consisting of a morphism `a : T ⟶ Y` and an open subspace of the fibre
product `T ×_Y X` whose projection to `T` is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.of :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (Z : OpenSubspace (pullback a f)),
    IsFinite (Z.ι ≫ pullback.fst a f) → FinitePart f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.ofι :
  ∀ {S : Scheme.{u}} {X Y T W : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (ι : W ⟶ pullback a f) [IsOpenImmersion ι],
    IsFinite (ι ≫ pullback.fst a f) → FinitePart f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.pr :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T), p.Z.X ⟶ T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.pr_eq :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T), p.pr = p.Z.ι ≫ pullback.fst p.a f)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.spec :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T), IsOpenImmersion p.Z.ι ∧ IsFinite p.pr)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.over :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → Over S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.map :
  ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y},
    FinitePart f T → (T' ⟶ T) → FinitePart f T')
