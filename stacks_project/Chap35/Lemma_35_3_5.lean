/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Amitsur.Acyclic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.3.5: if the structure map `R → A` admits an `R`-algebra section, then the
extended Amitsur cochain complex with coefficients in any `R`-module `M` is acyclic. -/
@[stacks 023L] #check (@Algebra.Amitsur.extended.acyclicOfSection :
  (R A M : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup M] → [Module R M] → (A →ₐ[R] R) →
      (Algebra.Amitsur.extended R A M).Acyclic)
