/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Dominance of the global-sections morphism

This module records dominance properties of the canonical morphism from a scheme to the spectrum
of its global sections.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsSchemeTheoreticallyDominant

/-- The canonical morphism from a scheme to the spectrum of its global sections is
scheme-theoretically dominant. -/
@[instance]
theorem toSpecΓ (X : Scheme.{u}) :
    IsSchemeTheoreticallyDominant X.toSpecΓ := sorry

end AlgebraicGeometry.IsSchemeTheoreticallyDominant

namespace AlgebraicGeometry.Scheme

/-- For a quasi-compact scheme, the structure-sheaf map of its canonical morphism to the
spectrum of global sections is a monomorphism. -/
@[instance]
theorem mono_toSpecΓ_c (X : Scheme.{u}) [CompactSpace X] :
    Mono X.toSpecΓ.c := sorry

end AlgebraicGeometry.Scheme
