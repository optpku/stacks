/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrictSlice.Construction
public import ReasLib.CategoryTheory.Bicategory.StrictPseudofunctor.Inverse
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence between the two full-subbicategory strict slices

The canonical forward and reverse repackaging strict pseudofunctors are strict inverses.
This file exposes both the computational round-trip API and the standard biequivalence
interfaces.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace ObjectProperty.FullSubbicategory.StrictSlice

variable {D : Type u} [Bicategory.{w, v} D] [Bicategory.Strict D]
variable (P : ObjectProperty D) (X : P.FullSubbicategory)

namespace toAmbient.ofAmbient

/-- Repackaging after forgetting the property witnesses recovers an internal strict-slice
object. -/
@[simp]
theorem obj (S : Bicategory.StrictSlice X) :
    (ofAmbient P X).obj ((toAmbient P X).obj S) = S := sorry

/-- Repackaging after forgetting the property witnesses recovers an internal strict-slice
morphism, up to endpoint transport. -/
@[simp]
theorem map
    {S T : Bicategory.StrictSlice X} (f : S ⟶ T) :
    (ofAmbient P X).map ((toAmbient P X).map f) ≍ f := sorry

/-- Repackaging after forgetting the property witnesses recovers an internal strict-slice
`2`-morphism, up to endpoint transport. -/
@[simp]
theorem map₂
    {S T : Bicategory.StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    (ofAmbient P X).map₂ ((toAmbient P X).map₂ eta) ≍ eta := sorry

end toAmbient.ofAmbient

namespace ofAmbient.toAmbient

/-- Forgetting the property witnesses after repackaging recovers an ambient strict-slice
object. -/
@[simp]
theorem obj (S : (P.strictSlice X.1).FullSubbicategory) :
    (toAmbient P X).obj ((ofAmbient P X).obj S) = S := sorry

/-- Forgetting the property witnesses after repackaging recovers an ambient strict-slice
morphism, up to endpoint transport. -/
@[simp]
theorem map
    {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    (toAmbient P X).map ((ofAmbient P X).map f) ≍ f := sorry

/-- Forgetting the property witnesses after repackaging recovers an ambient strict-slice
`2`-morphism, up to endpoint transport. -/
@[simp]
theorem map₂
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    (toAmbient P X).map₂ ((ofAmbient P X).map₂ eta) ≍ eta := sorry

end ofAmbient.toAmbient

/-- The canonical forward and reverse strict-slice repackaging pseudofunctors are strict
inverses. -/
theorem isStrictInverse :
    StrictPseudofunctor.IsStrictInverse (toAmbient P X) (ofAmbient P X) := sorry

/-- The canonical functor from the internal strict slice to the ambient full subbicategory is
a biequivalence. -/
instance toAmbient.isBiequivalence :
    Pseudofunctor.IsBiequivalence (toAmbient P X).toPseudofunctor := sorry

/-- The canonical repackaging functor from the ambient full subbicategory to the internal
strict slice is a biequivalence. -/
instance ofAmbient.isBiequivalence :
    Pseudofunctor.IsBiequivalence (ofAmbient P X).toPseudofunctor := sorry

/- Consumers that need explicit weak-inverse data can apply
`StrictPseudofunctor.IsStrictInverse.toWeakInverse` directly to `isStrictInverse`; no second data
owner is introduced here. -/

end ObjectProperty.FullSubbicategory.StrictSlice

end CategoryTheory
