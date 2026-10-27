/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap67.Lemma_67_22_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_26_1_FiberStalkCohenMacaulay

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay

/-!
# Cohen–Macaulay morphisms of algebraic spaces

Typed compatibility checks for the shared Cohen–Macaulay morphism API.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.fiberEtaleLocalRing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X),
    Type u)

#check (AlgebraicGeometry.AlgebraicSpace.fiberEtaleLocalRing_def :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X),
    fiberEtaleLocalRing f xbar =
      (etaleLocalRing X xbar ⧸
        Ideal.map (etaleLocalRingMap f xbar)
          (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))))

#check (AlgebraicGeometry.AlgebraicSpace.fiberEtaleLocalRing.instCommRing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X),
    CommRing (fiberEtaleLocalRing f xbar))

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X),
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayAt_iff_forallEtaleSquareAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkCohenMacaulay f x)

#check (AlgebraicGeometry.AlgebraicSpace.fiberStalkCohenMacaulay_ofOverGermHom_iff :
  ∀ {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left),
    fiberStalkCohenMacaulay (ofOverGermHom h u) ↔
      CohenMacaulayRing (h.left.fiberStalkAt u))

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt.flatAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : CohenMacaulayAt f x),
    FlatAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (hflat : FlatAt f x)
    (hQ : existsEtaleSquareAt fiberStalkCohenMacaulay f x),
    CohenMacaulayAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulay_iff_forall_cohenMacaulayAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    CohenMacaulay f ↔ ∀ x : Points X, CohenMacaulayAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f],
    (∀ x : Points X, CohenMacaulayAt f x) ∧ Flat f)

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay.instFlat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f],
    Flat f)

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    CohenMacaulay (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay.ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.CohenMacaulay h.left],
    CohenMacaulay (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.fibersCohenMacaulay :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.fibersCohenMacaulay_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y),
    fibersCohenMacaulay f b ↔
      ∀ v : V.left,
        hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
          (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v))

#check (AlgebraicGeometry.AlgebraicSpace.fibersCohenMacaulay.apply :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    {b : ofOver V ⟶ Y} (h : fibersCohenMacaulay f b) (v : V.left),
    hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v))

end AlgebraicGeometry.AlgebraicSpace
