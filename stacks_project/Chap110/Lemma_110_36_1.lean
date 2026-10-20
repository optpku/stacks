/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.IsEpi.ZeroDimensional
import StacksCheckRecall

universe u

/- Lemma 110.36.1: there exists an epimorphism of local rings of dimension `0` which is
not a surjection. -/
@[stacks 06RI] #check
  (RingHom.exists_isLocalRing_krullDimLE_zero_isEpi_not_surjective :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S)
      (_ : IsLocalRing R) (_ : IsLocalRing S) (_ : Ring.KrullDimLE 0 R)
      (_ : Ring.KrullDimLE 0 S),
      Algebra.IsEpi R S ∧ ¬ Function.Surjective (algebraMap R S))
