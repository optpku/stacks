/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import ReasLib.RingTheory.DirectLimit.Module.FinitePresentation
public import ReasLib.RingTheory.DirectLimit.Module.Transport
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of finite-module approximations

This leaf separates the module-descent step from the construction of a ring
approximation.  Once a finite-type approximation already has bijective stage
base-change maps, a finitely presented limiting module can be placed over that
same approximation.
-/

@[expose] public section

universe u v w x

namespace Ring.DirectLimit.Algebra.Approximation.Module

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- A finite-type ring approximation with bijective stage base-change maps
supports a finite-module approximation over a tail of that same ring
approximation for every finitely presented limiting module. -/
@[stacks 00R1 "finite module approximation existence"]
theorem exists_over_tail
    (A : FiniteType f)
    (h_bijective : A.toHom.baseChange_bijective)
    {M : Type x} [AddCommGroup M] [_root_.Module S M]
    [_root_.Module.FinitePresentation S M] :
    ∃ (i₀ : A.index) (B : Module f M), B.toFiniteType = A.tail i₀ := sorry

/-- A finitely presented ring homomorphism and a finitely presented limiting
module admit a common finite-module approximation. The index and ring stages
live in `max u v`, and the module stages live in `max u v x`. -/
@[stacks 00R1 "finite module approximation existence"]
theorem exists_of_finitePresentation
    (f : R →+* S) (h_finitePresentation : f.FinitePresentation)
    {M : Type x} [AddCommGroup M] [_root_.Module S M]
    [_root_.Module.FinitePresentation S M] :
    Nonempty (Module.{u, v, x, max u v x, max u v, max u v, max u v} f M) := sorry

end Ring.DirectLimit.Algebra.Approximation.Module
