/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Opens.IntersectionProduct

/-!
# Explicit separatedness bridges for affine opens
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Intersections of affine opens are affine when supplied an explicit separatedness witness for
the ambient scheme. -/
@[stacks 01KW "affine intersection explicit separatedness"]
theorem IsAffineOpen.inf_of_isSeparated
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hX : X.IsSeparated) :
    IsAffineOpen (U ⊓ V) := sorry

/-- The intersection of two opens maps as a closed immersion to their product when supplied an
explicit separatedness witness for the ambient scheme. -/
@[stacks 01KP "closed intersection explicit separatedness"]
theorem Scheme.Opens.isClosedImmersion_interToProduct_of_isSeparated
    (U V : X.Opens) (hX : X.IsSeparated) :
    IsClosedImmersion (Scheme.Opens.interToProduct U V) := sorry

/-- Lemma 26.21.16 (1): affine opens in the source of a separated morphism to a separated scheme
have affine intersection. -/
@[stacks 01KW "affine intersection over a separated base"]
theorem Scheme.Hom.isAffineOpen_inf
    (f : X ⟶ S) [IsSeparated f] [S.IsSeparated]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := sorry

/-- Lemma 26.21.16 (2): the intersection of two opens in the source of a separated morphism to a
separated scheme maps as a closed immersion to their product. -/
@[stacks 01KW "closed intersection inside the product"]
theorem Scheme.Hom.interToProduct_isClosedImmersion
    (f : X ⟶ S) [IsSeparated f] [S.IsSeparated] (U V : X.Opens) :
    IsClosedImmersion (Scheme.Opens.interToProduct U V) := sorry

end AlgebraicGeometry
