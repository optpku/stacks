/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.RingHom.ULift
public import ReasLib.RingTheory.FiniteFree

@[expose] public section

/-!
# Ind-finite-free ring homomorphisms

This file owns the ring-map predicate for filtered colimits of finite-free
algebras.  The arbitrary presentation universe is exposed through `Raw`, while
the ordinary predicate fixes the canonical endpoint universe.

@stack 0DCR
-/

open CategoryTheory MorphismProperty

universe u v w

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The representation-level filtered-colimit predicate for finite-free ring
maps.  The chapter phrase `filtered colimit of finite-free algebras` is a
ring-map property, so `IndFiniteFree` follows the existing `IndSmooth`/`IndEtale`
namespace pattern; `Raw` is the only layer that exposes presentation-universe
bookkeeping. -/
abbrev IndFiniteFree.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1}
    (toMorphismProperty FiniteFree) (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is ind-finite-free when it is a filtered colimit of finite-free
maps. -/
@[stacks 0DCR "filtered colimits of finite-free algebras"]
abbrev IndFiniteFree (f : R →+* A) : Prop :=
  IndFiniteFree.Raw.{u, v, max u v} f

end

namespace IndFiniteFree

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size filtered presentation induces the canonical
ind-finite-free predicate. -/
theorem ofRaw (f : R →+* A) (h : IndFiniteFree.Raw.{u, v, w} f) :
    f.IndFiniteFree := sorry
/- Proof strategy: use the universe-lowering comparison for `RingHom.ulift` and
the canonical endpoint specialization of `MorphismProperty.ind`. -/

/-- A finite-free ring map is ind-finite-free. -/
theorem ofFiniteFree (f : R →+* A) (hf : f.FiniteFree) :
    f.IndFiniteFree := sorry
/- Proof strategy: apply `MorphismProperty.le_ind` to the one-stage filtered
presentation and transport `hf` through `RingHom.toMorphismProperty`. -/

end

end IndFiniteFree

end RingHom
