/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.LocalConditions
public import Mathlib.Logic.Small.Basic

/-!
# Small codes for morphisms of descent objects

An actual small covering family and actual small local Hom codes give an
injection from completion morphisms into a small product. Smallness is derived
from that specified injection, with no existence-based size placeholder.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uF vF w

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A concrete small family refining a supplied actual covering sieve. -/
structure SmallRefinement {U : C} (R : J.Cover U) where
  Index : Type w
  object : Index → C
  arrow : ∀ i, object i ⟶ U
  member : ∀ i, R (arrow i)
  covering : Sieve.ofArrows object arrow ∈ J U

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

/-- Restrict an actual completion morphism and compare its local endpoints
to the original local models stored by the two descent objects. -/
def localHom {U : C} {a b : Object J F U} (φ : a ⟶ b)
    {V : C} (f : V ⟶ U) (ha : a.cover f) (hb : b.cover f) :
    (unitFunctor J F V).obj (a.datum.obj ⟨V, f, ha⟩) ⟶
      (unitFunctor J F V).obj (b.datum.obj ⟨V, f, hb⟩) :=
  (localComparisonIso J F a ⟨V, f, ha⟩).hom ≫
    (pullbackFunctor J F f).map φ ≫ (localComparisonIso J F b ⟨V, f, hb⟩).inv

/-- The original supplied prestack's actual descent preimage recovers the local Hom. -/
def localHomPreimage (hF : F.IsPrestack J) {U : C} {a b : Object J F U}
    (φ : a ⟶ b) {V : C} (f : V ⟶ U) (ha : a.cover f) (hb : b.cover f) :
    a.datum.obj ⟨V, f, ha⟩ ⟶ b.datum.obj ⟨V, f, hb⟩ :=
  unitPreimage J F hF (localHom J F φ f ha hb)

/-- The actual small local code product on the specified original covering family. -/
def HomCode {U : C} (a b : Object J F U) (R : SmallRefinement.{u, v, w} J (a.cover ⊓ b.cover))
    [∀ i, Small.{w} (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
      b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)] : Type w :=
  ∀ i : R.Index, Shrink.{w} (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
    b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)

/-- Encode an actual morphism using actual original local preimages and the
supplied actual local Hom shrink equivalences. -/
def encodeHom (hF : F.IsPrestack J) {U : C} {a b : Object J F U}
    (R : SmallRefinement.{u, v, w} J (a.cover ⊓ b.cover))
    [∀ i, Small.{w} (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
      b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)] (φ : a ⟶ b) :
    HomCode J F a b R :=
  fun i ↦ (equivShrink _) (localHomPreimage J F hF φ (R.arrow i)
    (R.member i).1 (R.member i).2)

/-- Equality of original local preimages on an actual covering family detects
the original completion morphism. The supplied prestack hypothesis is retained. -/
theorem encodeHom_injective (hF : F.IsPrestack J) {U : C} {a b : Object J F U}
    (R : SmallRefinement.{u, v, w} J (a.cover ⊓ b.cover))
    [∀ i, Small.{w} (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
      b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)] :
    Function.Injective (encodeHom J F hF R) := sorry

/-- Completion Hom smallness is witnessed by the specified injection into
the concrete small product, rather than an admitted size assertion. -/
theorem homSmall (hF : F.IsPrestack J) {U : C} (a b : Object J F U)
    (R : SmallRefinement.{u, v, w} J (a.cover ⊓ b.cover))
    [∀ i, Small.{w} (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
      b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)] : Small.{w} (a ⟶ b) :=
  small_of_injective (encodeHom_injective J F hF R)

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion
