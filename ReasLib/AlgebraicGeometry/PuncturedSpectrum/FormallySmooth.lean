/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FormallySmooth
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A B : Type u} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The target of a local homomorphism of Noetherian local rings has purity if
the source has depth at least two, the map is formally smooth for the target
maximal-ideal-adic topology, and the target has strictly larger Krull dimension. -/
theorem hasPurity_of_formallySmoothDepth
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A)
    (hfs : (algebraMap A B).formally_smooth_for_adic (IsLocalRing.maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B) :
    HasPurity B := sorry

end AlgebraicGeometry.PuncturedSpectrum
