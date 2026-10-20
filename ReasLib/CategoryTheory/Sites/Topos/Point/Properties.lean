/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Topos.Point.CounitSplit

/-!
# Direct-image properties of a topos point

This module packages the standard categorical and sheaf-theoretic properties
of the `Type`-valued direct image of a point.  The statements are split by
their mathematical role so that downstream users can import the individual
property rather than a Chapter 7 presentation file.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Lemma 7.32.10 (05UY) (2): the `Type`-valued direct image of a topos point is
faithful. -/
@[stacks 05UY "(2)"]
instance typePushforward_faithful
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.Faithful := sorry

/-- Lemma 7.32.10 (05UY) (3): the direct image of a topos point sends a surjective
map of types to a locally surjective map of sheaves. -/
@[stacks 05UY "(3)"]
theorem typePushforward_map_isLocallySurjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w}
    (f : E ⟶ E') (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (p.typePushforward.map f) := sorry

/-- Lemma 7.32.10 (05UY) (4): the direct image of a topos point preserves
coequalizers. -/
@[stacks 05UY "(4)"]
instance typePushforward_preservesCoequalizers
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesColimitsOfShape WalkingParallelPair p.typePushforward := sorry

/-- Lemma 7.32.10 (05UY) (5): if direct image sends a map of types to a locally
injective map of sheaves, then the original map is injective. -/
@[stacks 05UY "(5)"]
theorem typePushforward_reflectsInjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w}
    (f : E ⟶ E') (hf : Sheaf.IsLocallyInjective (p.typePushforward.map f)) :
    Function.Injective f := sorry

/-- Lemma 7.32.10 (05UY) (6): if direct image sends a map of types to a locally
surjective map of sheaves, then the original map is surjective. -/
@[stacks 05UY "(6)"]
theorem typePushforward_reflectsSurjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w}
    (f : E ⟶ E') (hf : Sheaf.IsLocallySurjective (p.typePushforward.map f)) :
    Function.Surjective f := sorry

/-- Lemma 7.32.10 (05UY) (7): the `Type`-valued direct image of a topos point
reflects isomorphisms. -/
@[stacks 05UY "(7)"]
instance typePushforward_reflectsIsomorphisms
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.ReflectsIsomorphisms := sorry

end CategoryTheory.MorphismOfTopoiIn
