/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Presheaf Module Notation

This module owns the conventional notation for the canonical category of modules over a
ring-valued presheaf.  It is deliberately independent of stalks, sheafification, and categorical
properties of the module category, so those APIs can import the notation without importing an
unrelated construction.
-/

@[expose] public section

open CategoryTheory

universe w v u

/-- `PMod(𝒪)` is the canonical category of presheaves of modules over the ring-valued presheaf
`𝒪`. -/
@[stacks 006Q "presheaf-module category notation"]
notation:max "PMod(" 𝒪 ")" => PresheafOfModules 𝒪

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{w})

