/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.OverOpen
public import ReasLib.AlgebraicGeometry.Scheme.Spectrum.OpenComplement
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Algebraic spaces isomorphic over an ideal complement

Specialize the relative open-isomorphism category to an affine Noetherian base.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of algebraic spaces locally of finite type over `Spec A` whose restriction
to `Spec A ∖ V(I)` is isomorphic to that open. -/
abbrev SpecComplement (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :=
  LocallyOfFiniteTypeOverOpen (Scheme.idealComplementOpens I)

end AlgebraicGeometry.AlgebraicSpace
