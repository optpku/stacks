/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.RingTheory.RingHom.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.14

@stack 02JL
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.14 (1): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is integral, then `R → S` is integral. This is
exactly the canonical mathlib theorem `RingHom.isIntegral_ofLocalizationSpan`. -/
@[stacks 02JL "(1)"]
#check (@RingHom.isIntegral_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.IsIntegral)

/- Lemma 10.36.14 (2): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is finite, then `R → S` is finite. This is exactly
the canonical mathlib theorem `RingHom.finite_ofLocalizationSpan`. -/
@[stacks 02JL "(2)"]
#check (@RingHom.finite_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.Finite)
