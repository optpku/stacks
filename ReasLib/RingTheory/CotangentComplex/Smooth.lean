/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.RingTheory.CotangentComplex.HomologyZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of a smooth algebra

The cotangent complex of a smooth algebra is isomorphic in the derived category to
its module of Kähler differentials concentrated in degree zero.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Smooth A B]

/-- The cotangent complex of a smooth algebra is isomorphic in the derived category
to its module of Kähler differentials concentrated in degree zero. -/
@[stacks 08R5]
theorem isIsomorphic_single_kaehler_of_smooth :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (ModuleCat.of B Ω[B⁄A])) :=
  sorry

/-- If `A → B` is smooth, then the André-Quillen homology of `L_{B/A}` vanishes in
every nonzero cohomological degree. -/
theorem homology_isZero_of_ne_zero_of_smooth {n : ℤ} (hn : n ≠ 0) :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

/-- If `A → B` is smooth, then the canonical cochain comparison `L_{B/A} ⟶ Ω[B⁄A][0]`
is a quasi-isomorphism. -/
instance augmentation_quasiIso_of_smooth : QuasiIso (augmentation A B) :=
  sorry

/-- If `A → B` is smooth, then the image of the canonical cochain comparison
`L_{B/A} ⟶ Ω[B⁄A][0]` is an isomorphism in `D(B)`. -/
instance map_augmentation_isIso_of_smooth :
    IsIso (DerivedCategory.Q.map (augmentation A B)) :=
  sorry

end Algebra.CotangentComplex
