/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Sites.Types

/-!
# Type-valued images of a topos point

This module transports the inverse image, direct image, and adjunction of a point presented as a
morphism from the terminal topos through the canonical equivalence with `Type`.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

noncomputable section

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The inverse image of a point, viewed as a `Type`-valued functor. -/
abbrev typeInverseImage (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Sheaf J (Type w) ⥤ Type w :=
  p.inverseImage ⋙ typeEquiv.{w}.inverse

/-- The direct image of a point, viewed as a functor out of `Type`. -/
abbrev typePushforward (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Type w ⥤ Sheaf J (Type w) :=
  typeEquiv.{w}.functor ⋙ p.pushforward

/-- The Type-valued inverse and direct images of a point form the adjunction transported through
`typeEquiv`. -/
abbrev typeAdjunction (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typeInverseImage ⊣ p.typePushforward :=
  p.adjunction.comp typeEquiv.{w}.symm.toAdjunction

/-- The `Type`-valued inverse image of a topos point preserves finite limits.

This is the transport of the left exactness built into `MorphismOfTopoiIn`
through the canonical equivalence with `Type`; terminal preservation is then
available to typeclass search as a special case. -/
instance typeInverseImage_preservesFiniteLimits
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesFiniteLimits p.typeInverseImage := sorry

/-- Lemma 7.32.10 (05UY) (1): the `Type`-valued direct image of a point is a
right adjoint, hence preserves arbitrary limits and is left exact.

The concrete adjunction remains `p.typeAdjunction`; this instance exposes
only the reusable Prop-valued right-adjoint interface. -/
@[stacks 05UY "(1)"]
noncomputable instance typePushforward_isRightAdjoint
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.IsRightAdjoint := sorry

end CategoryTheory.MorphismOfTopoiIn
