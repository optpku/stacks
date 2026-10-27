/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth

/-!
# The object properties of smooth families of curves

`𝒞urves^{smooth}` and `𝒞urves^{smooth, 1}` are the full subcategories of
families of curves whose structure morphisms are smooth, respectively smooth of
relative dimension 1. Membership expresses the classifying morphism factoring
through the corresponding open substack.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smooth :
    ∀ (S : Scheme.{u}),
    ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smooth_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smooth S P ↔ AlgebraicSpace.Smooth (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_smooth :
    ∀ (S : Scheme.{u}),
    (smooth S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1 :
    ∀ (S : Scheme.{u}),
    ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_smoothDim1 :
    ∀ (S : Scheme.{u}),
    (smoothDim1 S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1_le_smooth :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smoothDim1 S P → smooth S P)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
