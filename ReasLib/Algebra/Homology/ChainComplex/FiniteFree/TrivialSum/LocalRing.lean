/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.TrivialSum
public import ReasLib.RingTheory.Depth.Ext
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Trivial finite free sums over local rings

The public statements use `FiniteFreeComplex.ExactInPositiveDegrees`, so the
display bound and the chain-complex exactness convention remain encapsulated
by the finite-free-complex owner.
-/

@[expose] public section

universe u

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {e : ℕ}

/-- An exact-in-positive-degrees finite free complex over a Noetherian local
ring of depth zero is a finite sum of a degree-zero finite free complex and
identity disks. -/
@[stacks 00MY]
theorem isTrivialSum_of_exact_of_depth_zero [IsNoetherianRing R]
    (C : _root_.FiniteFreeComplex R e) (hexact : C.ExactInPositiveDegrees)
    (hdepth : moduleDepth R R = 0) :
    IsTrivialSum C.toChainComplex := sorry

/-- An exact-in-positive-degrees finite free complex over an Artinian local
ring is a finite sum of a degree-zero finite free complex and identity disks. -/
@[stacks 00MU]
theorem isTrivialSum_of_exact_of_artinian [IsArtinianRing R]
    (C : _root_.FiniteFreeComplex R e) (hexact : C.ExactInPositiveDegrees) :
    IsTrivialSum C.toChainComplex := sorry

end FiniteFreeComplex
