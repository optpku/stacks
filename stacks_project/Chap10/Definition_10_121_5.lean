/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Lattice.Distance
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import StacksCheckRecall

/-!
# Distance between lattices

@stack 02MG
-/

@[expose] public section

universe u v w

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]
variable (M M' : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K M']

/- Definition 10.121.5 (Stacks `02MG`): canonical recall of the reusable lattice-distance owner. -/
@[stacks 02MG]
#check (Submodule.latticeDistance M M' : ℤ)

@[stacks 02MG "lattice distance owner"]
#check @Submodule.latticeDistance
@[stacks 02MG "lattice distance specification"]
#check @Submodule.latticeDistance_def
