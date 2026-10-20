/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Fiber
public import ReasLib.RingTheory.Etale.Weakly
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etaleness of finitely presented weakly etale algebras

This leaf owns the weakly-etale finite-presentation criterion.  It is kept
separate from tensor-square criteria so downstream imports follow the actual
mathematical hypotheses.
@stack 0CKP
-/

@[expose] public section

universe u v

namespace Algebra.WeaklyEtale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A finitely presented weakly etale algebra is etale. -/
@[stacks 0CKP "finitely presented weakly etale algebras are etale"]
theorem etale_of_finitePresentation [Algebra.WeaklyEtale A B]
    [Algebra.FinitePresentation A B] : Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.WeaklyEtale.formallyUnramified (inferInstance : Algebra.WeaklyEtale A B)
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Algebra.WeaklyEtale
