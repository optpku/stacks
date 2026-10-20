/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of higher direct images to an open

@stack 01E5

The functor-level comparison is the reusable owner.  The ordinary higher-direct-image statement
is its degreewise source-facing projection; both are kept as propositions until a concrete
base-change isomorphism is proved in the derived pushforward layer.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Restriction

variable {X Y : RingedSpace.{u}}

/-- The derived pushforward restriction comparison over an open `V ⊆ Y`. -/
@[stacks 01E5 "derived restriction comparison for higher direct image"]
theorem derived_isomorphic
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic
      (moduleDerivedPushforward f ⋙ moduleRestrictionToOpenDerived Y V)
      (moduleRestrictionToOpenDerived X (preimageOpen f V) ⋙
        moduleDerivedPushforward (restrictedMorphismToOpen f V)) := sorry

/-- Lemma 20.7.4 (01E5) (2): bounded-below derived pushforward commutes with restriction to an
open subspace. -/
@[stacks 01E5 "bounded-below derived pushforward commutes with open restriction"]
theorem boundedBelow_isomorphic
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic
      (moduleDerivedPushforwardPlus f ⋙ moduleRestrictionToOpenDerivedPlus Y V)
      (moduleRestrictionToOpenDerivedPlus X (preimageOpen f V) ⋙
        moduleDerivedPushforwardPlus (restrictedMorphismToOpen f V)) := sorry

/-- Lemma 20.7.4 (01E5) (1): restriction of a degree-`p` higher direct image to `V` agrees with the
higher direct image of the restricted module along the restricted morphism. -/
@[stacks 01E5 "restriction of a higher direct image to an open"]
theorem object_isomorphic
    (f : X ⟶ Y) (V : Opens Y.carrier) (p : ℕ) (F : X.Modules) :
    IsIsomorphic
      ((moduleRestrictionToOpen Y V).obj (higherDirectImageModule f F p))
      (higherDirectImageModule (restrictedMorphismToOpen f V)
        ((moduleRestrictionToOpen X (preimageOpen f V)).obj F) p) := sorry

end AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Restriction

end
