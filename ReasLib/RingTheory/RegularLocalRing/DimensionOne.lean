/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent dimension of a regular local ring

This leaf exposes the finite-dimensional specialization of Mathlib's regular-local
cotangent-space identity.  The generic `d`-version is the reusable owner; the one-dimensional
name is retained as a source-facing bridge for the chapter.
-/

@[expose] public section

universe u

open IsLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A regular local ring has cotangent-space dimension equal to its Krull dimension, expressed at
a natural finite dimension `d`. -/
@[stacks 00P9 "finite-dimensional regular-local cotangent space"]
theorem finrank_cotangentSpace_eq_of_dim (d : ℕ)
    (hdim : ringKrullDim R = d) :
    Module.finrank (ResidueField R) (CotangentSpace R) = d := sorry

/-- The dimension-one specialization used in Lemma 10.119.3 (Stacks `00P9`). -/
@[stacks 00P9 "regular-local cotangent dimension"]
theorem finrank_cotangentSpace_eq_one (hdim : ringKrullDim R = 1) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 1 := sorry

end IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Source-facing bridge for the one-dimensional regular-local cotangent-space computation. -/
@[stacks 00P9 "source bridge"]
theorem finrank_cotangentSpace_eq_one_of_regular_dim_one
    (hdim : ringKrullDim R = 1) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 1 := sorry
