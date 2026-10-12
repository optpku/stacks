/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of change-of-rings functors

This leaf records the canonical additive and zero-morphism-preserving
structure of change-of-rings functors at the lowest module-category layer, so
derived and homological consumers do not need to rebuild it locally.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ModuleCat.ExtendScalars

/-- Extension of scalars along a map of commutative rings is additive. -/
@[stacks 00M8 "extension-of-scalars additivity"]
instance additive
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, v, w} f).Additive where
  map_add {X Y} g h := by
    -- Local instance justification (defeq pin): the base-change map uses the algebra induced by `f`.
    letI := f.toAlgebra
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add (A := S) g.hom h.hom

/-- Extension of scalars preserves zero morphisms at arbitrary source, target, and module
universes.  This belongs to the change-of-rings owner rather than to a particular complex model. -/
@[stacks 00M8 "extension-of-scalars zero morphisms"]
instance (priority := 100) preservesZeroMorphisms
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, v, w} f).PreservesZeroMorphisms := by
  infer_instance

end ModuleCat.ExtendScalars

namespace ModuleCat.CoextendScalars

/-- Coextension of scalars along a ring homomorphism is additive. -/
noncomputable instance additive
    {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.coextendScalars.{u, v, w} f).Additive := sorry

end ModuleCat.CoextendScalars
