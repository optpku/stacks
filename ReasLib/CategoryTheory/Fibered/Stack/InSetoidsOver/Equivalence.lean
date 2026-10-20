/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence data for morphisms of stacks in setoids

An equivalence over the base between stacks in setoids is first packaged at the stack-in-groupoids
layer, then lifted through the full subbicategory selecting thin fibers. No additional inverse or
coherence data are chosen here.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace StackOver.Setoids.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Setoids J}

/-- Package equivalence of the underlying based functor as a bicategorical equivalence of
stacks in setoids. -/
@[stacks 02ZK "setoid-stack lifted equivalence data"]
noncomputable def asEquivalenceOf {F : X ⟶ Y} (hF : IsEquivalence F) : X ≌ Y :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (StackOver.Groupoids.Hom.asEquivalenceOf
      ((isEquivalence_iff_toGroupoidsMor F).mp hF))

/-- The forward morphism of `asEquivalenceOf hF` is the original morphism of stacks in
setoids. -/
@[simp, stacks 02ZK "setoid-stack lifted equivalence forward readout"]
theorem asEquivalenceOf.hom {F : X ⟶ Y} (hF : IsEquivalence F) :
    (asEquivalenceOf hF).hom = F := sorry

namespace IsEquivalence

/-- Fixed-forward-morphism equivalence data for a morphism of stacks in setoids. -/
@[stacks 02ZK "setoid-stack fixed-morphism equivalence data"]
noncomputable def toOnHom {F : X ⟶ Y} (hF : IsEquivalence F) :
    Bicategory.Equivalence.OnHom F :=
  Bicategory.Equivalence.OnHom.ofEquivalence (asEquivalenceOf hF)

/-- Reassembling the fixed-forward-morphism data gives the canonical lifted equivalence. -/
@[simp, stacks 02ZK "setoid-stack equivalence reconstruction"]
theorem toOnHom.toEquivalence {F : X ⟶ Y} (hF : IsEquivalence F) :
    hF.toOnHom.toEquivalence = asEquivalenceOf hF := sorry

/-- Bicategorical equivalence data on a morphism of stacks in setoids imply equivalence of its
underlying based functor. -/
@[stacks 02ZK "setoid-stack equivalence predicate readout"]
theorem ofOnHom {F : X ⟶ Y} (hF : Bicategory.Equivalence.OnHom F) :
    IsEquivalence F := sorry

end IsEquivalence

/- Data audit: the stack-in-groupoids owner supplies the inverse, unit, and counit;
`equivalenceOfAmbient` only retains them in the full subbicategory selected by the setoid-fiber
property. Deferred content is confined to property and bicategorical coherence proofs. -/

end StackOver.Setoids.Hom

end CategoryTheory
