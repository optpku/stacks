/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0

/-!
# The object property of smooth curves with universally trivial pushforward of 𝒪

`𝒞urves^{smooth, h0}` is the full subcategory of families of curves that are
smooth and lie in `𝒞urves^{h0, 1}`. Membership is the source-facing packaging
of a classifying morphism factoring through that open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0 :
    ∀ S : Scheme.{u}, ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      smoothH0 S P ↔
        (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
            IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
          AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_smoothH0 :
    ∀ S : Scheme.{u}, (smoothH0 S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0_le_h0Dim1 :
    ∀ {S : Scheme.{u}} (P : Obj S), smoothH0 S P → h0Dim1 S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0_smooth :
    ∀ {S : Scheme.{u}} (P : Obj S), smoothH0 S P → AlgebraicSpace.Smooth (hom P))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
