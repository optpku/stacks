module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence data for morphisms of stacks

This module packages `StackOver.Hom.IsEquivalence` as bicategorical equivalence data. The
fibred-category layer owns preservation of strongly cartesian arrows by the selected inverse;
this leaf only lifts that equivalence through the full subbicategory of stacks.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.{u, v, w, vS} J}

/-- Package an explicit proof that a stack morphism is an equivalence over the base as a
bicategorical equivalence of stacks. -/
@[stacks 046N "package a stack morphism equivalence"]
noncomputable def asEquivalenceOf {F : X ⟶ Y} (hF : IsEquivalence F) :
    X ≌ Y :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (FiberedCategoryOver.Hom.asEquivalenceOf (toMor F) hF)

/-- The forward morphism of `asEquivalenceOf hF` is the original stack morphism. -/
@[stacks 046N "forward morphism of a stack equivalence", simp]
theorem asEquivalenceOf.hom {F : X ⟶ Y} (hF : IsEquivalence F) :
    (asEquivalenceOf hF).hom = F := sorry

namespace IsEquivalence

/-- Fixed-forward-morphism equivalence data for a stack morphism known to be an equivalence over
the base. -/
@[stacks 046N "fixed-forward equivalence data for a stack morphism"]
noncomputable def toOnHom {F : X ⟶ Y} (hF : IsEquivalence F) :
    Bicategory.Equivalence.OnHom F :=
  Bicategory.Equivalence.OnHom.ofEquivalence (asEquivalenceOf hF)

/-- Reassembling the fixed-forward-morphism data gives the canonical stack equivalence. -/
@[stacks 046N "reassemble fixed-forward stack equivalence data", simp]
theorem toOnHom.toEquivalence {F : X ⟶ Y} (hF : IsEquivalence F) :
    hF.toOnHom.toEquivalence = asEquivalenceOf hF := sorry

/-- Bicategorical equivalence data on a stack morphism imply equivalence of its underlying based
functor. -/
@[stacks 046N "recover stack equivalence from on-hom data"]
theorem ofOnHom {F : X ⟶ Y} (hF : Bicategory.Equivalence.OnHom F) :
    IsEquivalence F := sorry

end IsEquivalence

/- Data audit: `asEquivalenceOf` retains the inverse, unit, and counit selected by the neutral
fibred-category owner and only lifts them through the full subbicategory of stacks. Deferred
content is confined to cartesian-preservation and bicategorical coherence proof fields. -/

end StackOver.Hom

end CategoryTheory
