/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Cotangent dimension of a regular local ring

This leaf exposes the finite-dimensional specialization of Mathlib's regular-local
cotangent-space identity. Specialize the generic `d`-version to `1` for dimension one.
-/

@[expose] public section

universe u

open IsLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A regular local ring has cotangent-space dimension equal to its Krull dimension, expressed at
a natural finite dimension `d`. -/
theorem finrank_cotangentSpace_eq_of_dim (d : ℕ)
    (hdim : ringKrullDim R = d) :
    Module.finrank (ResidueField R) (CotangentSpace R) = d := by
  have h := (iff_finrank_cotangentSpace R).mp ‹IsRegularLocalRing R›
  rw [hdim] at h
  exact_mod_cast h

end IsRegularLocalRing
