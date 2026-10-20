/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Functorial
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# Existence of Grothendieck Spectral Sequences

This file specializes the neutral realization API to the canonical bounded-below right-derived
functors.  The hypotheses are the source-level ones: two left-exact functors, enough injectives
in the first two abelian categories, and right acyclicity of the images of injective objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [EnoughInjectives A] [EnoughInjectives B]
variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The canonical Grothendieck spectral-sequence realization attached to `F`, `G`, and `X`.
The two derived functors are Mathlib's total bounded-below right-derived functors. -/
@[stacks 015N "canonical Grothendieck spectral sequence"]
abbrev canonical (X : DerivedCategory.Plus A) :=
  SpectralSequence G (Bounded.functor F) (Bounded.functor (F ⋙ G)) X

/-- Two additive left-exact functors between abelian categories admit a Grothendieck
spectral-sequence realization for every bounded-below derived object when the first two
categories have enough injectives and the first functor sends injectives to objects that are
right-acyclic for the second functor. -/
@[stacks 015N]
theorem nonempty
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hAcyclic : ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I))
    (X : DerivedCategory.Plus A) : Nonempty (canonical F G X) := sorry

/-- Functorial form of the Grothendieck construction: a morphism of bounded-below derived
objects admits compatible choices of realizations and a map between them. -/
@[stacks 015N "functoriality"]
theorem existsMap
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hAcyclic : ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I))
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    ∃ (S : canonical F G X) (T : canonical F G Y),
      Nonempty (SpectralSequence.Map f S T) := sorry

/-- Grothendieck realizations can be chosen coherently and functorially in the bounded-below
derived input. -/
@[stacks 015N "functorial Grothendieck spectral sequence"]
theorem functorial
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hAcyclic : ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I)) :
    Nonempty (SpectralSequence.Functorial G (Bounded.functor F)
      (Bounded.functor (F ⋙ G))) := sorry

end CategoryTheory.Functor.RightDerived.Grothendieck
