module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.TruncationSplitting.GlobalDimension
public import ReasLib.RingTheory.DedekindDomain.GlobalDimension

@[expose] public section

/-!
# Splitting Bounded Derived Objects over Dedekind Domains

@stack 0EX0

The uniform higher-Ext vanishing supplied by the global dimension of a Dedekind domain specializes
the generic shifted-cohomology splitting theorem for bounded derived objects.

@stack 0EX0
-/

noncomputable section

universe u

namespace DerivedCategory.ShiftedCohomology.Split

open CategoryTheory
open CategoryTheory.Limits

/-- Stacks 0EX0: every bounded derived object of modules over a Dedekind domain is a finite
biproduct of its shifted cohomology objects over a suitable interval. -/
@[stacks 0EX0 "bounded derived splitting"]
theorem ofDedekindDomain
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (K : DerivedCategory.Bounded (ModuleCat.{u} R)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ on (ModuleCat.{u} R) K.obj a b) := sorry

end DerivedCategory.ShiftedCohomology.Split
