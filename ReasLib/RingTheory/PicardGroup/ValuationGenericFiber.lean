/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.Algebra.Module.FinitePresentation.ValuationRing
public import ReasLib.RingTheory.RegularLocalRing.SerreCondition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Picard groups of valuation-ring generic fibers

This leaf owns the source-faithful generic-fiber conclusion for a local flat essentially finite
type algebra over a valuation ring.  The source tensors are kept explicit; `Ideal.Fiber` views
are comparison presentations and are not used as a second theorem owner.

@stack 0DLQ
-/

open scoped TensorProduct
open IsLocalRing

universe u v

namespace ValuationRing

variable {R : Type u} {A : Type v} [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing A] [Algebra R A] [IsLocalRing A]
variable [IsLocalHom (algebraMap R A)] [Module.Flat R A]
variable [Algebra.EssFiniteType R A]

/-- Lemma 15.122.3 (0DLQ): a local flat essentially finite type algebra over a valuation ring
with regular closed fiber has trivial Picard group on its generic fiber. -/
@[stacks 0DLQ "Lemma 15.122.3: trivial Picard group of the generic fiber"]
theorem subsingletonPicardGroupGenericFiber_of_regularClosedFiber
    [IsRegularRing (A ⊗[R] ResidueField R)] :
    Subsingleton (CommRing.Pic (A ⊗[R] FractionRing R)) := sorry
-- Proof strategy: descend an invertible generic-fiber module to a finitely
-- presented `A`-module, quotient its `R`-torsion, and use the valuation-ring
-- criterion to make the quotient `R`-flat.  Closed-fiber regularity then gives
-- a finite free resolution over `A`; compare its Euler characteristic and
-- determinant after base change to show that the original Picard class is one.

end ValuationRing

end
