/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt

/-!
# Pointwise étaleness of morphisms of algebraic spaces

A morphism of algebraic spaces is étale at a point when it is étale after
restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace


#check (EtaleAt : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
  (X ⟶ Y) → Points X → Prop)
#check (etaleAt_iff : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  (x : Points X), EtaleAt f x ↔
    ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
      IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Etale (i ≫ f))
#check (EtaleAt.of : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
  {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X},
  [IsOpenImmersion i] → x ∈ Set.range (Points.map i) →
    [Etale (i ≫ f)] → EtaleAt f x)
#check (etaleAt_of_etale : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  (f : X ⟶ Y), [Etale f] → (x : Points X) → EtaleAt f x)

end AlgebraicGeometry.AlgebraicSpace
