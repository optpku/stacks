/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points of scheme modules

This file owns the stalkwise weakly-associated-point predicate and locus for a
module on a scheme. The definitions apply to every scheme module.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}

/-- A point is weakly associated to a scheme module when the maximal ideal of its local ring is
weakly associated to the module stalk. -/
@[stacks 056L]
def weaklyAssociatedAt (F : X.Modules) (x : X) : Prop :=
  Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk x)
    (@RingedSpace.stalkModuleCat X.toRingedSpace F x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- The set of weakly associated points of a scheme module. -/
@[stacks 056L]
def weakAss (F : X.Modules) : Set X :=
  F.weaklyAssociatedAt

/-- Membership in `weakAss F` is the stalkwise weak-association predicate. -/
theorem mem_weakAss_iff (F : X.Modules) (x : X) :
    x ∈ F.weakAss ↔ F.weaklyAssociatedAt x :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules
