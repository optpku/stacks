module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat

/-!
# Derived categories of modules

This leaf supplies the standard derived-category model for module categories
over arbitrary rings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uA w

namespace ModuleCat

/-- The standard derived-category structure on `ModuleCat A`, used to pass from cochain
complexes of `A`-modules to `DerivedCategory (ModuleCat A)`. -/
instance hasDerivedCategory (A : Type uA) [Ring A] :
    HasDerivedCategory.{max (w + 1) uA} (ModuleCat.{w} A) :=
  HasDerivedCategory.standard (ModuleCat.{w} A)

/-- The preferred `Type w` Ext universe for modules over a ring `A : Type uA`.

Mathlib deliberately does not register `hasExt_of_enoughProjectives` as a global instance,
because several smallness universes may be available for the same category.  This named owner
lets derived-category specializations pin the canonical module choice without repeating the
universe plumbing at each call site. -/
@[stacks 0EWX "module Ext universe support"]
theorem hasExt (A : Type uA) [Ring A] [Small.{w} A] :
    CategoryTheory.HasExt.{w} (ModuleCat.{w} A) := sorry

/-- Forgetting an `A`-module to its additive commutative group preserves finite colimits.

The corresponding all-colimits theorem in Mathlib is universe-polymorphic, but typeclass search
cannot always infer its size parameters when the carrier and ring universes differ.  This owner
pins the canonical finite interface once, so exact-derived constructions need no local instance.
-/
@[stacks 09CZ "exact module-to-additive forgetful functor"]
noncomputable instance forget₂PreservesFiniteColimits (A : Type uA) [Ring A] :
    Limits.PreservesFiniteColimits
      (forget₂ (ModuleCat.{w} A) AddCommGrpCat.{w}) := sorry

/-- The exact derived functor forgetting a module structure to an additive commutative group.

This is the canonical target-side forgetful functor for comparisons between derived module
colimits and additive lower shrieks.  Its finite-limit and finite-colimit instances come from the
standard module-category limits/colimits owners, so downstream statements do not rebuild them.
-/
@[stacks 09CZ "derived module-to-additive forgetful functor"]
noncomputable abbrev forgetDerived (A : Type uA) [Ring A] :
    DerivedCategory (ModuleCat.{w} A) ⥤ DerivedCategory AddCommGrpCat.{w} :=
  (forget₂ (ModuleCat.{w} A) AddCommGrpCat.{w}).mapDerivedCategory

end ModuleCat
