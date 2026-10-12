/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly

/-!
# Weakly pre-adic and weakly adic rings

A linearly topologized ring is weakly pre-adic when some ideal has the closures of
its powers open and forming a fundamental system of neighborhoods of `0`. It is
weakly adic when it is weakly pre-adic and complete, including separated.
-/

@[expose] public section

universe u

#check
  (@TopologicalRing.IsWeaklyPreadicRing :
    ∀ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R), Prop)
#check
  (@TopologicalRing.IsWeaklyAdicRing :
    ∀ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R), Prop)
