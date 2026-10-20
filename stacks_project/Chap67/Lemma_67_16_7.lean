/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.PartialSection
import StacksCheckRecall

/-!
# Scheme-theoretic image of a partial section

A section of a separated morphism of algebraic spaces over a quasi-compact open
immersion has scheme-theoretic image mapping isomorphically to the target over
that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.16.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a separated morphism
of algebraic spaces over `S`. Let `ιV : V ⟶ Y` be a quasi-compact open
immersion, and let `s : V ⟶ X` be a section of `f` over `V`. If `ι : Y' ⟶ X`
is a scheme-theoretic image of `s`, then `Y' ⟶ Y` is an isomorphism over `V`. -/
@[stacks 0CP3] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.isIso_openInverseImageTo_of_section :
    ∀ {S : Scheme.{u}}
    {X Y V Y' : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
    (s : V ⟶ X) (hs : s ≫ f = ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
    [IsSchemeTheoreticImage s toImage ι],
    IsIso (openInverseImageTo (ι ≫ f) ιV))
