/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.SymmDiff
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap79.Lemma_79_12_2_FinitePart
public import stacks_project.Chap79.Lemma_79_12_4

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Boolean

/-! # Boolean operations on compatible finite-part opens -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.FinitePart AlgebraicGeometry.AlgebraicSpace.FinitePart.Point
universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.castZMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    {p q : Point f T} (h : p.a = q.a),
    C(Points (pullback p.a f), Points (pullback q.a f)))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.castZ :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    {p q : Point f T} (h : p.a = q.a),
    Opens (Points (pullback p.a f)))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.castZ_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    {p q : Point f T} (h : p.a = q.a),
    castZ h = Opens.comap (castZMap h) q.Z)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.castZ_carrier :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    {p q : Point f T} (h : p.a = q.a),
    (castZ h).carrier = castZMap h ⁻¹' q.Z.carrier)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.closedImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p : Point f T),
    IsClosedImmersion (OpenSubspace.fromOpens p.Z).ι)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.isOpen_sdiff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsOpen (p.Z.carrier \ (castZ h).carrier))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.isClosed_inter :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsClosed (p.Z.carrier ∩ (castZ h).carrier))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.union_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsFinite ((OpenSubspace.fromOpens (p.Z ⊔ castZ h)).ι ≫ pullback.fst p.a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.union :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.inter_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsFinite ((OpenSubspace.fromOpens (p.Z ⊓ castZ h)).ι ≫ pullback.fst p.a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.inter :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsFinite ((OpenSubspace.fromOpens (Opens.mk (p.Z.carrier \ (castZ h).carrier) (isOpen_sdiff p q h))).ι ≫ pullback.fst p.a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.mul :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_isOpen :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsOpen (symmDiff p.Z.carrier (castZ h).carrier))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    IsFinite ((OpenSubspace.fromOpens (Opens.mk (symmDiff p.Z.carrier (castZ h).carrier) (add_isOpen p q h))).ι ≫ pullback.fst p.a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.empty_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (a : ofOver T ⟶ Y),
    IsFinite ((OpenSubspace.fromOpens ((⊥ : Opens (Points (pullback a f))))).ι ≫ pullback.fst a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.empty :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (a : ofOver T ⟶ Y),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.univ_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [IsFinite f] (a : ofOver T ⟶ Y),
    IsFinite ((OpenSubspace.fromOpens ((⊤ : Opens (Points (pullback a f))))).ι ≫ pullback.fst a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.univ :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [IsFinite f] (a : ofOver T ⟶ Y),
    Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.union_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.union q h).a = p.a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.union_Z :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.union q h).Z = p.Z ⊔ castZ h)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.inter_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.inter q h).a = p.a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.inter_Z :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.inter q h).Z = p.Z ⊓ castZ h)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.sdiff q h).a = p.a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff_Z :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.sdiff q h).Z = Opens.mk (p.Z.carrier \ (castZ h).carrier) (isOpen_sdiff p q h))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.add q h).a = p.a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_eq_union_sdiff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    p.add q h = (p.sdiff q h).union (q.sdiff p h.symm) h)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_eq_symmDiff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    (p.add q h).Z.carrier = symmDiff p.Z.carrier (castZ h).carrier)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.mul_eq_inter :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p q : Point f T) (h : p.a = q.a),
    p.mul q h = p.inter q h)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.empty_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (a : ofOver T ⟶ Y),
    (empty a : Point f T).a = a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.empty_Z :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (a : ofOver T ⟶ Y),
    (empty a : Point f T).Z = ⊥)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.univ_a :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [IsFinite f] (a : ofOver T ⟶ Y),
    (univ a : Point f T).a = a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.univ_Z :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [IsFinite f] (a : ofOver T ⟶ Y),
    (univ a : Point f T).Z = ⊤)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.add_self :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] (p : Point f T),
    p.add p rfl = (empty p.a : Point f T))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff_eq_mul_add_one :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] [IsFinite f] (p q : Point f T)
    (h : p.a = q.a),
    p.sdiff q h = p.mul ((univ p.a : Point f T).add q h) rfl)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.sdiff_swap_eq_add_one_mul :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    [Separated f] [IsFinite f] (p q : Point f T)
    (h : p.a = q.a),
    q.sdiff p h.symm = ((univ p.a : Point f T).add p rfl).mul q h)
