/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.LinearFactor
import StacksCheckRecall

/-!
# Lemma 15.21.2

@stack 0530
-/

@[expose] public section

open Polynomial

universe u

@[stacks 0530]
#check fun {R : Type u} [CommRing R] {P : R[X]} (hP : P.Monic) ↦
  (Polynomial.Monic.exists_finiteFree_extension_with_monic_linearFactor hP :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (a : R') (Q : R'[X]),
      (algebraMap R R').FiniteFree ∧ Q.Monic ∧
        P.map (algebraMap R R') = (X - C a) * Q)

#check @Polynomial.Monic.finite_adjoinRoot
#check @Polynomial.Monic.free_adjoinRoot
#check @AdjoinRoot.isRoot_root
#check @RingHom.finiteFree_algebraMap
