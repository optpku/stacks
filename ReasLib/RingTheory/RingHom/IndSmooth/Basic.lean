/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.RingHom.ULift

/-!
# Ind-smooth ring maps

@stack 07C3

This leaf defines filtered colimits of smooth ring maps directly from a ring
homomorphism. The common-universe lift is explicit, so the public owner does
not encode the map through temporary algebra instances.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u v w

namespace RingHom

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The representation-level ind-smooth predicate with an arbitrary universe
for the filtered presentation. -/
abbrev IndSmooth.Raw (f : R →+* A) : Prop :=
  CategoryTheory.MorphismProperty.ind.{w, max u v, max u v + 1}
    (toMorphismProperty Smooth) (CommRingCat.ofHom f.ulift.{v, u})

/-- Lemma 10.127.4, tag `07C3`: a ring map is ind-smooth when it is a
filtered colimit of smooth algebras. The public owner uses the canonical
endpoint universe; arbitrary presentation sizes belong to `IndSmooth.Raw`. -/
@[stacks 07C3 "ind-smooth ring maps"]
abbrev IndSmooth (f : R →+* A) : Prop :=
  IndSmooth.Raw.{u, v, max u v} f

namespace IndSmooth

/-- An arbitrary-size categorical presentation induces the canonical
ind-smooth predicate. -/
theorem ofRaw (f : R →+* A) (h : IndSmooth.Raw.{u, v, w} f) :
    f.IndSmooth := sorry

/-- A smooth ring map is ind-smooth. -/
theorem ofSmooth (f : R →+* A) (hf : f.Smooth) : f.IndSmooth := sorry

/-- An ind-smooth ring map is flat. -/
theorem flat {f : R →+* A} (hf : f.IndSmooth) : f.Flat := sorry

end IndSmooth

end RingHom
